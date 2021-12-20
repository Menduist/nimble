# Copyright (C) Dominik Picheta. All rights reserved.
# BSD License. Look at license.txt for more info.

import system except TResult

import os, tables, strtabs, json, algorithm, sets, uri, sugar, sequtils, osproc
import std/options as std_opt

import strutils except toLower
from unicode import toLower
from sequtils import toSeq
from strformat import fmt

import nimblepkg/packageinfo, nimblepkg/version, nimblepkg/tools,
       nimblepkg/download, nimblepkg/config, nimblepkg/common,
       nimblepkg/publish, nimblepkg/options, nimblepkg/packageparser,
       nimblepkg/cli, nimblepkg/packageinstaller, nimblepkg/reversedeps,
       nimblepkg/nimscriptexecutor, nimblepkg/init

import nimblepkg/nimscriptwrapper

proc refresh(options: Options) =
  ## Downloads the package list from the specified URL.
  ##
  ## If the download is not successful, an exception is raised.
  let parameter =
    if options.action.typ == actionRefresh:
      options.action.optionalURL
    else:
      ""

  if parameter.len > 0:
    if parameter.isUrl:
      let cmdLine = PackageList(name: "commandline", urls: @[parameter])
      fetchList(cmdLine, options)
    else:
      if parameter notin options.config.packageLists:
        let msg = "Package list with the specified name not found."
        raise newException(NimbleError, msg)

      fetchList(options.config.packageLists[parameter], options)
  else:
    # Try each package list in config
    for name, list in options.config.packageLists:
      fetchList(list, options)

proc buildFromDir(
  pkgInfo: PackageInfo, paths, args: seq[string],
  options: Options
) =
  ## Builds a package as specified by ``pkgInfo``.
  # Handle pre-`build` hook.
  let
    realDir = pkgInfo.getRealDir()
    pkgDir = pkgInfo.myPath.parentDir()
  cd pkgDir: # Make sure `execHook` executes the correct .nimble file.
    if not execHook(options, actionBuild, true):
      raise newException(NimbleError, "Pre-hook prevented further execution.")

  if pkgInfo.bin.len == 0:
    raise newException(NimbleError,
        "Nothing to build. Did you specify a module to build using the" &
        " `bin` key in your .nimble file?")
  var
    binariesBuilt = 0
    args = args
  args.add "-d:NimblePkgVersion=" & pkgInfo.version
  for path in paths:
    args.add("--path:" & path.quoteShell)
  if options.verbosity >= HighPriority:
    # Hide Nim hints by default
    args.add("--hints:off")
  if options.verbosity == SilentPriority:
    # Hide Nim warnings
    args.add("--warnings:off")

  let binToBuild =
    # Only build binaries specified by user if any, but only if top-level package,
    # dependencies should have every binary built.
    if options.isInstallingTopLevel(pkgInfo.myPath.parentDir()):
      options.getCompilationBinary(pkgInfo).get("")
    else: ""
  for bin, src in pkgInfo.bin:
    # Check if this is the only binary that we want to build.
    if binToBuild.len != 0 and binToBuild != bin:
      if bin.extractFilename().changeFileExt("") != binToBuild:
        continue

    let outputOpt = "-o:" & pkgInfo.getOutputDir(bin).quoteShell
    display("Building", "$1/$2 using $3 backend" %
            [pkginfo.name, bin, pkgInfo.backend], priority = HighPriority)

    let outputDir = pkgInfo.getOutputDir("")
    if not dirExists(outputDir):
      createDir(outputDir)

    let input = realDir / src.changeFileExt("nim")
    # `quoteShell` would be more robust than `\"` (and avoid quoting when
    # un-necessary) but would require changing `extractBin`
    let cmd = "$# $# --colors:on --noNimblePath $# $# $#" % [
      getNimBin(options).quoteShell, pkgInfo.backend, join(args, " "),
      outputOpt, input.quoteShell]
    try:
      doCmd(cmd)
      binariesBuilt.inc()
    except NimbleError:
      let currentExc = (ref NimbleError)(getCurrentException())
      let exc = newException(BuildFailed, "Build failed for package: " &
                             pkgInfo.name)
      let (error, hint) = getOutputInfo(currentExc)
      exc.msg.add("\n" & error)
      exc.hint = hint
      raise exc

  if binariesBuilt == 0:
    raiseNimbleError(
      "No binaries built, did you specify a valid binary name?"
    )

  # Handle post-`build` hook.
  cd pkgDir: # Make sure `execHook` executes the correct .nimble file.
    discard execHook(options, actionBuild, false)

proc removePkgDir(dir: string, options: Options) =
  ## Removes files belonging to the package in ``dir``.
  try:
    var nimblemeta = parseFile(dir / "nimblemeta.json")
    if not nimblemeta.hasKey("files"):
      raise newException(JsonParsingError,
                         "Meta data does not contain required info.")
    for file in nimblemeta["files"]:
      removeFile(dir / file.str)

    removeFile(dir / "nimblemeta.json")

    # If there are no files left in the directory, remove the directory.
    if toSeq(walkDirRec(dir)).len == 0:
      removeDir(dir)
    else:
      display("Warning:", ("Cannot completely remove $1. Files not installed " &
              "by nimble are present.") % dir, Warning, HighPriority)

    if nimblemeta.hasKey("binaries"):
      # Remove binaries.
      for binary in nimblemeta["binaries"]:
        removeFile(options.getBinDir() / binary.str)

      # Search for an older version of the package we are removing.
      # So that we can reinstate its symlink.
      let (pkgName, _) = getNameVersion(dir)
      let pkgList = getInstalledPkgsMin(options.getPkgsDir(), options)
      var pkgInfo: PackageInfo
      if pkgList.findPkg((pkgName, newVRAny()), pkgInfo):
        pkgInfo = pkgInfo.toFullInfo(options)
        for bin, src in pkgInfo.bin:
          let symlinkDest = pkgInfo.getOutputDir(bin)
          let symlinkFilename = options.getBinDir() / bin.extractFilename
          discard setupBinSymlink(symlinkDest, symlinkFilename, options)
    else:
      display("Warning:", ("Cannot completely remove $1. Binary symlinks may " &
                          "have been left over in $2.") %
                          [dir, options.getBinDir()])
  except OSError, JsonParsingError:
    display("Warning", "Unable to read nimblemeta.json: " &
            getCurrentExceptionMsg(), Warning, HighPriority)
    if not options.prompt("Would you like to COMPLETELY remove ALL files " &
                          "in " & dir & "?"):
      raise NimbleQuit(msg: "")
    removeDir(dir)

proc vcsRevisionInDir(dir: string): string =
  ## Returns current revision number of HEAD if dir is inside VCS, or nil in
  ## case of failure.
  var cmd = ""
  if dirExists(dir / ".git"):
    cmd = "git -C " & quoteShell(dir) & " rev-parse HEAD"
  elif dirExists(dir / ".hg"):
    cmd = "hg --cwd " & quoteShell(dir) & " id -i"

  if cmd.len > 0:
    try:
      let res = doCmdEx(cmd)
      if res.exitCode == 0:
        result = string(res.output).strip()
    except:
      discard

proc installFromDir(dir: string, options: Options,
                    paths: seq[string], url: string, pkgInfo: var PackageInfo) =
  ## Returns where package has been installed to, together with paths
  ## to the packages this package depends on.
  ## The return value of this function is used by
  ## ``processDeps`` to gather a list of paths to pass to the nim compiler.

  # Handle pre-`install` hook.
  cd dir: # Make sure `execHook` executes the correct .nimble file.
    if not execHook(options, actionInstall, true):
      raise newException(NimbleError, "Pre-hook prevented further execution.")

  let realDir = pkgInfo.getRealDir()
  let binDir = options.getBinDir()

  display("Installing", "$1@$2" % [pkginfo.name, pkginfo.specialVersion],
          priority = HighPriority)

  # Build before removing an existing package (if one exists). This way
  # if the build fails then the old package will still be installed.
  if pkgInfo.bin.len > 0:
    let flags = if options.action.typ in {actionInstall, actionPath, actionUninstall, actionDevelop}:
                  options.action.passNimFlags
                else:
                  @[]
    buildFromDir(pkgInfo, paths, "-d:release" & flags, options)

  # Don't copy artifacts if project local deps mode and "installing" the top level package
  if not (options.localdeps and options.isInstallingTopLevel(dir)):
    let pkgDestDir = pkgInfo.getPkgDest(options)
    if dirExists(pkgDestDir) and fileExists(pkgDestDir / "nimblemeta.json"):
      let msg = "$1@$2 already exists. Overwrite?" %
                [pkgInfo.name, pkgInfo.specialVersion]
      if not options.prompt(msg):
        return

      # Remove reverse deps.
      let pkgInfo = getPkgInfo(pkgDestDir, options)
      options.nimbleData.removeRevDep(pkgInfo)

      removePkgDir(pkgDestDir, options)
      # Remove any symlinked binaries
      for bin, src in pkgInfo.bin:
        # TODO: Check that this binary belongs to the package being installed.
        when defined(windows):
          removeFile(binDir / bin.changeFileExt("cmd"))
          removeFile(binDir / bin.changeFileExt(""))
        else:
          removeFile(binDir / bin)

    createDir(pkgDestDir)
    # Copy this package's files based on the preferences specified in PkgInfo.
    var filesInstalled = initHashSet[string]()
    iterInstallFiles(realDir, pkgInfo, options,
      proc (file: string) =
        createDir(changeRoot(realDir, pkgDestDir, file.splitFile.dir))
        let dest = changeRoot(realDir, pkgDestDir, file)
        filesInstalled.incl copyFileD(file, dest)
    )

    # Copy the .nimble file.
    let dest = changeRoot(pkgInfo.myPath.splitFile.dir, pkgDestDir,
                          pkgInfo.myPath)
    filesInstalled.incl copyFileD(pkgInfo.myPath, dest)

    var binariesInstalled = initHashSet[string]()
    if pkgInfo.bin.len > 0:
      # Make sure ~/.nimble/bin directory is created.
      createDir(binDir)
      # Set file permissions to +x for all binaries built,
      # and symlink them on *nix OS' to $nimbleDir/bin/
      for bin, src in pkgInfo.bin:
        let binDest =
          # Issue #308
          if dirExists(pkgDestDir / bin):
            bin & ".out"
          else: bin
        if fileExists(pkgDestDir / binDest):
          display("Warning:", ("Binary '$1' was already installed from source" &
                              " directory. Will be overwritten.") % bin, Warning,
                  MediumPriority)

        # Copy the binary file.
        createDir((pkgDestDir / binDest).parentDir())
        filesInstalled.incl copyFileD(pkgInfo.getOutputDir(bin),
                                      pkgDestDir / binDest)

        # Set up a symlink.
        let symlinkDest = pkgDestDir / binDest
        let symlinkFilename = options.getBinDir() / bin.extractFilename
        for filename in setupBinSymlink(symlinkDest, symlinkFilename, options):
          binariesInstalled.incl(filename)

    let vcsRevision = vcsRevisionInDir(realDir)

    # Save a nimblemeta.json file.
    saveNimbleMeta(pkgDestDir, url, vcsRevision, filesInstalled,
                  binariesInstalled)

    # Save the nimble data (which might now contain reverse deps added in
    # processDeps).
    saveNimbleData(options)

    # update package path to point to installed directory rather than the temp directory
    pkgInfo.myPath = dest
  else:
    display("Warning:", "Skipped copy in project local deps mode", Warning)

  pkgInfo.isInstalled = true

  # Return the dependencies of this package (mainly for paths).
  display("Success:", pkgInfo.name & " installed successfully.",
          Success, HighPriority)

  # Run post-install hook now that package is installed. The `execHook` proc
  # executes the hook defined in the CWD, so we set it to where the package
  # has been installed.
  cd pkgInfo.myPath.splitFile.dir:
    discard execHook(options, actionInstall, false)

proc getDownloadInfo*(pv: PkgTuple, options: Options,
                      doPrompt: bool): (DownloadMethod, string,
                                        Table[string, string]) =
  if pv.name.isURL:
    let (url, metadata) = getUrlData(pv.name)
    return (checkUrlType(url), url, metadata)
  else:
    var pkg: Package
    if getPackage(pv.name, options, pkg):
      let (url, metadata) = getUrlData(pkg.url)
      return (pkg.downloadMethod.getDownloadMethod(), url, metadata)
    else:
      # If package is not found give the user a chance to refresh
      # package.json
      if doPrompt and
          options.prompt(pv.name & " not found in any local packages.json, " &
                         "check internet for updated packages?"):
        refresh(options)

        # Once we've refreshed, try again, but don't prompt if not found
        # (as we've already refreshed and a failure means it really
        # isn't there)
        return getDownloadInfo(pv, options, false)
      else:
        raise newException(NimbleError, "Package not found.")

proc installIteration(packages: seq[PkgTuple],
             options: Options,
             doPrompt = true): seq[PackageInfo] =
  type
    InstallConstraint =
      tuple[
        source: string,
        version: VersionRange
      ]

    InstallInfo =
      tuple[
        package: PackageInfo,
        version: Version,
        downloadDir: string
      ]

  var
    pkgList = getInstalledPkgsMin(options.getPkgsDir(), options)
    installConstraints: Table[string, seq[InstallConstraint]]
    dependencies: Table[string, seq[string]]
    installInfo: Table[string, InstallInfo]
    toProcess: seq[string]

  for package in packages:
    let constraintTuple = ("user", package.ver)
    if package.name == "nimrod" or package.name == "nim":
      let nimVer = getNimrodVersion(options)
      if not withinRange(nimVer, package.ver):
        let msg = "Unsatisfied dependency: " & package.name & " (" & $package.ver & ")"
        raise newException(NimbleError, msg)
      continue
    if package.name in installConstraints:
      installConstraints[package.name] &= constraintTuple
    else:
      installConstraints[package.name] = @[constraintTuple]
      toProcess.add(package.name)

  # For each thing to install:
  # - Create a version range using all constraints
  # - Get all deps, add constraint on each of them
  # - If a dep has already been installed, and we have a new incompatible
  #   constraint, put it back in the list
  while toProcess.len > 0:
    var packageName = toProcess[0]
    let packageConstraints = installConstraints[packageName]
    toProcess.delete(0)

    display("Checking",
            "$1 required by: $2" % [packageName, packageConstraints.mapIt(it.source & " (" & $it.version & ")").join(", ")],
            priority = HighPriority)

    # Compute versions constraints
    var
      combinedVersion = none(VersionRange)
      specialVersion = none(VersionRange)
    try:
      for constraint in packageConstraints:
        if constraint.version.kind == verSpecial:
          specialVersion =
            some(if specialVersion.isSome and specialVersion.get() != constraint.version:
              raise newException(NimbleError, "Non-compatible special versions")
            else:
              constraint.version)
        else:
          combinedVersion =
            some(if combinedVersion.isSome:
              combinedVersion.get().refine(constraint.version)
            else:
              constraint.version)
    except NimbleError:
      raise newException(NimbleError, "Cannot satisfy the dependencies on $1" % [packageName])

    var pkgTuple = (
      name: packageName,
      ver: if specialVersion.isSome: specialVersion.get() else: combinedVersion.get()
    )

    var package: PackageInfo

    if packageName in dependencies:
      # We already have ran this package before
      # clean it up from previous dependencies
      # and remove no longer used packages
      var noLongerRequired: seq[string]
      for otherPackage in dependencies[packageName]:
        installConstraints[otherPackage].keepItIf(it.source != packageName)
        if installConstraints[otherPackage].len == 0:
          noLongerRequired.add(otherPackage)
      dependencies.del(packageName)
      for otherPackage in noLongerRequired:
        dependencies.del(otherPackage)
        installInfo.del(otherPackage)
        installConstraints.del(otherPackage)


    var
      downloadDir: string
      downloadVersion: Version

    if not pkgList.findPkg(pkgTuple, package):
      # Not already installed
      # Download it to get it's metadata
      let (meth, url, metadata) = getDownloadInfo(pkgTuple, options, doPrompt)
      let subdir = metadata.getOrDefault("subdir")

      (downloadDir, downloadVersion) = downloadPkg(url, pkgTuple.ver, meth, subdir, options)
      package = getPkgInfo(downloadDir, options)

    if package.name != packageName:
      # We resolved the real package name

      # We have to replace the old name
      for otherDep in dependencies.keys():
        dependencies[otherDep].applyIt(if it == packageName: package.name else: it)

      installConstraints.del(packageName)

      if package.name in installConstraints:
        installConstraints[package.name] &= packageConstraints

        if package.name in installInfo and package.name notin toProcess:
          let currentVersion = installInfo[package.name].version
          # Check that our constraints are compatible
          # otherwise, recompute this package
          for constraint in packageConstraints:
            if not currentVersion.withinRange(constraint.version):
              toProcess.add(package.name)
              break
        continue
      else:
        # This is the first time we hear about this package
        # let's continue after renaming it correctly
        packageName = package.name
        installConstraints[packageName] = packageConstraints
        pkgTuple.name = packageName

        if pkgList.findPkg(pkgTuple, package):
          # The resolved package is already installed
          downloadDir = ""

    package = package.toFullInfo(options)

    # If we used a special version, check that the combined constraints
    # are also compatible
    if combinedVersion.isSome and not package.version.Version.withinRange(combinedVersion.get()):
      raise newException(NimbleError, "Cannot satisfy the dependencies on $1" % [packageName])

    if specialVersion.isSome:
      package.specialVersion = $specialVersion.get()

    installInfo[packageName] = (package: package, version: package.version.Version, downloadDir: downloadDir)

    # Check its deps
    var deps: seq[string]
    for dep in package.requires:
      if dep.name == "nimrod" or dep.name == "nim":
        let nimVer = getNimrodVersion(options)
        if not withinRange(nimVer, dep.ver):
          let msg = "Unsatisfied dependency: " & dep.name & " (" & $dep.ver & ")"
          raise newException(NimbleError, msg)

      else:
        var depPackage: PackageInfo
        let resolvedDep = dep.resolveAlias(options)
        let resolvedName =
          if pkgList.findPkg(resolvedDep, depPackage):
            depPackage.name
          else: resolvedDep.name

        let constraintTuple = (packageName, resolvedDep.ver)

        if resolvedName in installConstraints:
          # Adds our constraint
          if constraintTuple notin installConstraints[resolvedName]:
            installConstraints[resolvedName].add(constraintTuple)

            # Are we compatible?
            if resolvedName in installInfo and resolvedName notin toProcess:
              if not installInfo[resolvedName].version.withinRange(resolvedDep.ver):
                # No, recompute this package
                toProcess.add(resolvedName)
        else:
          # New package, add it
          installConstraints[resolvedName] = @[constraintTuple]
          toProcess.add(resolvedName)
        deps.add(resolvedName)
      dependencies[packageName] = deps

  # Install missing packages
  toProcess = toSeq(installInfo.keys())
  while toProcess.len > 0:
    let packageName = toProcess[0]
    toProcess.delete(0)

    var depPaths: seq[string]
    # Dumb dependency solver
    for dep in dependencies[packageName]:
      if dep in toProcess:
        toProcess.add(packageName)
        break
      depPaths.add(installInfo[dep].package.getRealDir())
    if packageName in toProcess: continue

    if installInfo[packageName].downloadDir.len == 0:
      # Already installed
      # Do this after the dependency solver
      continue

    # This will save output data to package directly
    installFromDir(installInfo[packageName].downloadDir, options, depPaths, "", installInfo[packageName].package)
    result.add installInfo[packageName].package

    for dep in dependencies[packageName]:
      addRevDep(options.nimbleData, (dep, $installInfo[dep].version), installInfo[packageName].package)

proc install(packages: seq[PkgTuple],
             options: Options,
             doPrompt = true): seq[PackageInfo] =
  if packages.len == 0:
    var pkgInfo = getPkgInfo(getCurrentDir(), options)
    result = installIteration(pkgInfo.requires, options, doPrompt)
    if not options.depsOnly:
      installFromDir(getCurrentDir(), options, result.mapIt(it.getRealDir()), "", pkgInfo)
      result.add(pkgInfo)
  else:
    result = installIteration(packages, options, doPrompt)

proc build(options: Options) =
  var pkgInfo = getPkgInfo(getCurrentDir(), options)
  nimScriptHint(pkgInfo)
  let deps = installIteration(pkginfo.requires, options)
  let paths = deps.map(dep => dep.getRealDir())
  var args = options.getCompilationFlags()
  buildFromDir(pkgInfo, paths, args, options)

proc execBackend(pkgInfo: PackageInfo, options: Options) =
  let
    bin = options.getCompilationBinary(pkgInfo).get("")
    binDotNim = bin.addFileExt("nim")
  if bin == "":
    raise newException(NimbleError, "You need to specify a file.")

  if not (fileExists(bin) or fileExists(binDotNim)):
    raise newException(NimbleError,
      "Specified file, " & bin & " or " & binDotNim & ", does not exist.")

  var pkgInfo = getPkgInfo(getCurrentDir(), options)
  nimScriptHint(pkgInfo)
  let deps = installIteration(pkginfo.requires, options)

  if not execHook(options, options.action.typ, true):
    raise newException(NimbleError, "Pre-hook prevented further execution.")

  var args = @["-d:NimblePkgVersion=" & pkgInfo.version]
  for dep in deps:
    args.add("--path:" & dep.getRealDir().quoteShell)
  if options.verbosity >= HighPriority:
    # Hide Nim hints by default
    args.add("--hints:off")
  if options.verbosity == SilentPriority:
    # Hide Nim warnings
    args.add("--warnings:off")
  for option in options.getCompilationFlags():
    args.add(option.quoteShell)

  let backend =
    if options.action.backend.len > 0:
      options.action.backend
    else:
      pkgInfo.backend

  if options.action.typ == actionCompile:
    display("Compiling", "$1 (from package $2) using $3 backend" %
            [bin, pkgInfo.name, backend], priority = HighPriority)
  else:
    display("Generating", ("documentation for $1 (from package $2) using $3 " &
            "backend") % [bin, pkgInfo.name, backend], priority = HighPriority)
  doCmd(getNimBin(options).quoteShell & " $# --noNimblePath $# $#" %
        [backend, join(args, " "), bin.quoteShell])
  display("Success:", "Execution finished", Success, HighPriority)

  # Run the post hook for action if it exists
  discard execHook(options, options.action.typ, false)

proc search(options: Options) =
  ## Searches for matches in ``options.action.search``.
  ##
  ## Searches are done in a case insensitive way making all strings lower case.
  assert options.action.typ == actionSearch
  if options.action.search == @[]:
    raise newException(NimbleError, "Please specify a search string.")
  if needsRefresh(options):
    raise newException(NimbleError, "Please run nimble refresh.")
  let pkgList = getPackageList(options)
  var found = false
  template onFound {.dirty.} =
    echoPackage(pkg)
    if pkg.alias.len == 0 and options.queryVersions:
      echoPackageVersions(pkg)
    echo(" ")
    found = true
    break forPkg

  for pkg in pkgList:
    block forPkg:
      for word in options.action.search:
        # Search by name.
        if word.toLower() in pkg.name.toLower():
          onFound()
        # Search by tag.
        for tag in pkg.tags:
          if word.toLower() in tag.toLower():
            onFound()

  if not found:
    display("Error", "No package found.", Error, HighPriority)

proc list(options: Options) =
  if needsRefresh(options):
    raise newException(NimbleError, "Please run nimble refresh.")
  let pkgList = getPackageList(options)
  for pkg in pkgList:
    echoPackage(pkg)
    if pkg.alias.len == 0 and options.queryVersions:
      echoPackageVersions(pkg)
    echo(" ")

proc listInstalled(options: Options) =
  var h = initOrderedTable[string, seq[string]]()
  let pkgs = getInstalledPkgsMin(options.getPkgsDir(), options)
  for x in pkgs.items():
    let
      pName = x.pkginfo.name
      pVer = x.pkginfo.specialVersion
    if not h.hasKey(pName): h[pName] = @[]
    var s = h[pName]
    add(s, pVer)
    h[pName] = s

  h.sort(proc (a, b: (string, seq[string])): int = cmpIgnoreCase(a[0], b[0]))
  for k in keys(h):
    echo k & "  [" & h[k].join(", ") & "]"

type VersionAndPath = tuple[version: Version, path: string]

proc listPaths(options: Options) =
  ## Loops over the specified packages displaying their installed paths.
  ##
  ## If there are several packages installed, only the last one (the version
  ## listed in the packages.json) will be displayed. If any package name is not
  ## found, the proc displays a missing message and continues through the list,
  ## but at the end quits with a non zero exit error.
  ##
  ## On success the proc returns normally.
  cli.setSuppressMessages(true)
  assert options.action.typ == actionPath

  if options.action.packages.len == 0:
    raise newException(NimbleError, "A package name needs to be specified")

  var errors = 0
  let pkgs = getInstalledPkgsMin(options.getPkgsDir(), options)
  for name, version in options.action.packages.items:
    var installed: seq[VersionAndPath] = @[]
    # There may be several, list all available ones and sort by version.
    for x in pkgs.items():
      let
        pName = x.pkginfo.name
        pVer = x.pkginfo.specialVersion
      if name == pName:
        var v: VersionAndPath
        v.version = newVersion(pVer)
        v.path = x.pkginfo.getRealDir()
        installed.add(v)

    if installed.len > 0:
      sort(installed, cmp[VersionAndPath], Descending)
      # The output for this command is used by tools so we do not use display().
      echo installed[0].path
    else:
      display("Warning:", "Package '$1' is not installed" % name, Warning,
              MediumPriority)
      errors += 1
  if errors > 0:
    raise newException(NimbleError,
        "At least one of the specified packages was not found")

proc join(x: seq[PkgTuple]; y: string): string =
  if x.len == 0: return ""
  result = x[0][0] & " " & $x[0][1]
  for i in 1 ..< x.len:
    result.add y
    result.add x[i][0] & " " & $x[i][1]

proc getPackageByPattern(pattern: string, options: Options): PackageInfo =
  ## Search for a package file using multiple strategies.
  if pattern == "":
    # Not specified - using current directory
    result = getPkgInfo(os.getCurrentDir(), options)
  elif pattern.splitFile.ext == ".nimble" and pattern.fileExists:
    # project file specified
    result = getPkgInfoFromFile(pattern, options)
  elif pattern.dirExists:
    # project directory specified
    result = getPkgInfo(pattern, options)
  else:
    # Last resort - attempt to read as package identifier
    let packages = getInstalledPkgsMin(options.getPkgsDir(), options)
    let identTuple = parseRequires(pattern)
    var skeletonInfo: PackageInfo
    if not findPkg(packages, identTuple, skeletonInfo):
      raise newException(NimbleError,
          "Specified package not found"
      )
    result = getPkgInfoFromFile(skeletonInfo.myPath, options)

# import std/jsonutils
proc `%`(a: Version): JsonNode = %a.string

# proc dump(options: Options, json: bool) =
proc dump(options: Options) =
  cli.setSuppressMessages(true)
  let p = getPackageByPattern(options.action.projName, options)
  var j: JsonNode
  var s: string
  let json = options.dumpMode == kdumpJson
  if json: j = newJObject()
  template fn(key, val) =
    if json:
      when val is seq[PkgTuple]:
        # jsonutils.toJson would work but is only available since 1.3.5, so we
        # do it manually.
        j[key] = newJArray()
        for (name, ver) in val:
          j[key].add %{
            "name": % name,
            # we serialize both: `ver` may be more convenient for tooling
            # (no parsing needed); while `str` is more familiar.
            "str": % $ver,
            "ver": %* ver,
          }
      else:
        j[key] = %*val
    else:
      if s.len > 0: s.add "\n"
      s.add key & ": "
      when val is string:
        s.add val.escape
      else:
        s.add val.join(", ").escape
  fn "name", p.name
  fn "version", p.version
  fn "author", p.author
  fn "desc", p.description
  fn "license", p.license
  fn "skipDirs", p.skipDirs
  fn "skipFiles", p.skipFiles
  fn "skipExt", p.skipExt
  fn "installDirs", p.installDirs
  fn "installFiles", p.installFiles
  fn "installExt", p.installExt
  fn "requires", p.requires
  fn "bin", toSeq(p.bin.keys)
  fn "binDir", p.binDir
  fn "srcDir", p.srcDir
  fn "backend", p.backend
  if json:
    s = j.pretty
  echo s

proc init(options: Options) =
  # Check whether the vcs is installed.
  let vcsBin = options.action.vcsOption
  if vcsBin != "" and findExe(vcsBin, true) == "":
    raise newException(NimbleError, "Please install git or mercurial first")

  # Determine the package name.
  let pkgName =
    if options.action.projName != "":
      options.action.projName
    else:
      os.getCurrentDir().splitPath.tail.toValidPackageName()

  # Validate the package name.
  validatePackageName(pkgName)

  # Determine the package root.
  let pkgRoot =
    if pkgName == os.getCurrentDir().splitPath.tail:
      os.getCurrentDir()
    else:
      os.getCurrentDir() / pkgName

  let nimbleFile = (pkgRoot / pkgName).changeFileExt("nimble")

  if fileExists(nimbleFile):
    let errMsg = "Nimble file already exists: $#" % nimbleFile
    raise newException(NimbleError, errMsg)

  if options.forcePrompts != forcePromptYes:
    display(
      "Info:",
      "Package initialisation requires info which could not be inferred.\n" &
      "Default values are shown in square brackets, press\n" &
      "enter to use them.",
      priority = HighPriority
    )
  display("Using", "$# for new package name" % [pkgName.escape()],
    priority = HighPriority)

  # Determine author by running an external command
  proc getAuthorWithCmd(cmd: string): string =
    let (name, exitCode) = doCmdEx(cmd)
    if exitCode == QuitSuccess and name.len > 0:
      result = name.strip()
      display("Using", "$# for new package author" % [result],
        priority = HighPriority)

  # Determine package author via git/hg or asking
  proc getAuthor(): string =
    if findExe("git") != "":
      result = getAuthorWithCmd("git config --global user.name")
    elif findExe("hg") != "":
      result = getAuthorWithCmd("hg config ui.username")
    if result.len == 0:
      result = promptCustom(options, "Your name?", "Anonymous")
  let pkgAuthor = getAuthor()

  # Declare the src/ directory
  let pkgSrcDir = "src"
  display("Using", "$# for new package source directory" % [pkgSrcDir.escape()],
    priority = HighPriority)

  # Determine the type of package
  let pkgType = promptList(
    options,
    """Package type?
Library - provides functionality for other packages.
Binary  - produces an executable for the end-user.
Hybrid  - combination of library and binary

For more information see https://goo.gl/cm2RX5""",
    ["library", "binary", "hybrid"]
  )

  # Ask for package version.
  let pkgVersion = promptCustom(options, "Initial version of package?", "0.1.0")
  validateVersion(pkgVersion)

  # Ask for description
  let pkgDesc = promptCustom(options, "Package description?",
    "A new awesome nimble package")

  # Ask for license
  # License list is based on:
  # https://www.blackducksoftware.com/top-open-source-licenses
  var pkgLicense = options.promptList(
    """Package License?
This should ideally be a valid SPDX identifier. See https://spdx.org/licenses/.
""", [
    "MIT",
    "GPL-2.0",
    "Apache-2.0",
    "ISC",
    "GPL-3.0",
    "BSD-3-Clause",
    "LGPL-2.1",
    "LGPL-3.0",
    "EPL-2.0",
    "AGPL-3.0",
    # This is what npm calls "UNLICENSED" (which is too similar to "Unlicense")
    "Proprietary",
    "Other"
  ])

  if pkgLicense.toLower == "other":
    pkgLicense = promptCustom(options,
      """Package license?
Please specify a valid SPDX identifier.""",
      "MIT"
    )

  if pkgLicense in ["GPL-2.0", "GPL-3.0", "LGPL-2.1", "LGPL-3.0", "AGPL-3.0"]:
    let orLater = options.promptList(
      "\"Or any later version\" clause?", ["Yes", "No"])
    if orLater == "Yes":
      pkgLicense.add("-or-later")
    else:
      pkgLicense.add("-only")

  # Ask for Nim dependency
  let nimDepDef = getNimrodVersion(options)
  let pkgNimDep = promptCustom(options, "Lowest supported Nim version?",
    $nimDepDef)
  validateVersion(pkgNimDep)

  createPkgStructure(
    (
      pkgName,
      pkgVersion,
      pkgAuthor,
      pkgDesc,
      pkgLicense,
      pkgSrcDir,
      pkgNimDep,
      pkgType
    ),
    pkgRoot
  )

  # Create a git or hg repo in the new nimble project.
  if vcsBin != "":
    let cmd = fmt"cd {pkgRoot} && {vcsBin} init"
    let ret: tuple[output: string, exitCode: int] = execCmdEx(cmd)
    if ret.exitCode != 0: quit ret.output

    var ignoreFile = if vcsBin == "git": ".gitignore" else: ".hgignore"
    var fd = open(joinPath(pkgRoot, ignoreFile), fmWrite)
    fd.write(pkgName & "\n")
    fd.close()

  display("Success:", "Package $# created successfully" % [pkgName], Success,
    HighPriority)

proc uninstall(options: Options) =
  if options.action.packages.len == 0:
    raise newException(NimbleError,
        "Please specify the package(s) to uninstall.")

  var pkgsToDelete: HashSet[PackageInfo]
  pkgsToDelete.init()
  # Do some verification.
  for pkgTup in options.action.packages:
    display("Looking", "for $1 ($2)" % [pkgTup.name, $pkgTup.ver],
            priority = HighPriority)
    let installedPkgs = getInstalledPkgsMin(options.getPkgsDir(), options)
    var pkgList = findAllPkgs(installedPkgs, pkgTup)
    if pkgList.len == 0:
      raise newException(NimbleError, "Package not found")

    display("Checking", "reverse dependencies", priority = HighPriority)
    for pkg in pkgList:
      # Check whether any packages depend on the ones the user is trying to
      # uninstall.
      if options.uninstallRevDeps:
        getAllRevDeps(options, pkg, pkgsToDelete)
      else:
        let
          revDeps = getRevDeps(options, pkg)
        var reason = ""
        for revDep in revDeps:
          if reason.len != 0: reason.add ", "
          reason.add("$1 ($2)" % [revDep.name, revDep.version])
        if reason.len != 0:
          reason &= " depend" & (if revDeps.len == 1: "s" else: "") & " on it"

        if len(revDeps - pkgsToDelete) > 0:
          display("Cannot", "uninstall $1 ($2) because $3" %
                  [pkgTup.name, pkg.specialVersion, reason], Warning, HighPriority)
        else:
          pkgsToDelete.incl pkg

  if pkgsToDelete.len == 0:
    raise newException(NimbleError, "Failed uninstall - no packages to delete")

  var pkgNames = ""
  for pkg in pkgsToDelete.items:
    if pkgNames.len != 0: pkgNames.add ", "
    pkgNames.add("$1 ($2)" % [pkg.name, pkg.specialVersion])

  # Let's confirm that the user wants these packages removed.
  let msg = ("The following packages will be removed:\n  $1\n" &
            "Do you wish to continue?") % pkgNames
  if not options.prompt(msg):
    raise NimbleQuit(msg: "")

  for pkg in pkgsToDelete:
    # If we reach this point then the package can be safely removed.

    # removeRevDep needs the package dependency info, so we can't just pass
    # a minimal pkg info.
    removeRevDep(options.nimbleData, pkg.toFullInfo(options))
    removePkgDir(options.getPkgsDir / (pkg.name & '-' & pkg.specialVersion),
                 options)
    display("Removed", "$1 ($2)" % [pkg.name, $pkg.specialVersion], Success,
            HighPriority)

  saveNimbleData(options)

proc listTasks(options: Options) =
  let nimbleFile = findNimbleFile(getCurrentDir(), true)
  nimscriptwrapper.listTasks(nimbleFile, options)

proc developFromDir(dir: string, options: Options) =
  cd dir: # Make sure `execHook` executes the correct .nimble file.
    if not execHook(options, actionDevelop, true):
      raise newException(NimbleError, "Pre-hook prevented further execution.")

  var pkgInfo = getPkgInfo(dir, options)
  if pkgInfo.bin.len > 0:
    if "nim" in pkgInfo.skipExt:
      raiseNimbleError("Cannot develop packages that are binaries only.")

    display("Warning:", "This package's binaries will not be compiled " &
            "nor symlinked for development.", Warning, HighPriority)

  # Overwrite the version to #head always.
  pkgInfo.specialVersion = "#head"

  if options.developLocaldeps:
    var optsCopy: Options
    optsCopy.forcePrompts = options.forcePrompts
    optsCopy.nimbleDir = dir / nimbledeps
    createDir(optsCopy.getPkgsDir())
    optsCopy.verbosity = options.verbosity
    optsCopy.action = Action(typ: actionDevelop)
    optsCopy.config = options.config
    optsCopy.nimbleData = %{"reverseDeps": newJObject()}
    optsCopy.pkgInfoCache = newTable[string, PackageInfo]()
    optsCopy.noColor = options.noColor
    optsCopy.disableValidation = options.disableValidation
    optsCopy.forceFullClone = options.forceFullClone
    optsCopy.startDir = dir
    optsCopy.nim = options.nim
    cd dir:
      discard installIteration(pkgInfo.requires, optsCopy)
  else:
    # Dependencies need to be processed before the creation of the pkg dir.
    discard installIteration(pkgInfo.requires, options)

  # Don't link if project local deps mode and "developing" the top level package
  if not (options.localdeps and options.isInstallingTopLevel(dir)):
    # This is similar to the code in `installFromDir`, except that we
    # *consciously* not worry about the package's binaries.
    let pkgDestDir = pkgInfo.getPkgDest(options)
    if dirExists(pkgDestDir) and fileExists(pkgDestDir / "nimblemeta.json"):
      let msg = "$1@$2 already exists. Overwrite?" %
                [pkgInfo.name, pkgInfo.specialVersion]
      if not options.prompt(msg):
        raise NimbleQuit(msg: "")
      removePkgDir(pkgDestDir, options)

    createDir(pkgDestDir)
    # The .nimble-link file contains the path to the real .nimble file,
    # and a secondary path to the source directory of the package.
    # The secondary path is necessary so that the package's .nimble file doesn't
    # need to be read. This will mean that users will need to re-run
    # `nimble develop` if they change their `srcDir` but I think it's a worthy
    # compromise.
    let nimbleLinkPath = pkgDestDir / pkgInfo.name.addFileExt("nimble-link")
    let nimbleLink = NimbleLink(
      nimbleFilePath: pkgInfo.myPath,
      packageDir: pkgInfo.getRealDir()
    )
    writeNimbleLink(nimbleLinkPath, nimbleLink)

    # Save a nimblemeta.json file.
    saveNimbleMeta(pkgDestDir, dir, vcsRevisionInDir(dir), nimbleLinkPath)

    # Save the nimble data (which might now contain reverse deps added in
    # processDeps).
    saveNimbleData(options)

    display("Success:", (pkgInfo.name & " linked successfully to '$1'.") %
            dir, Success, HighPriority)
  else:
    display("Warning:", "Skipping link in project local deps mode", Warning)

  # Execute the post-develop hook.
  cd dir:
    discard execHook(options, actionDevelop, false)

proc develop(options: Options) =
  if options.action.packages == @[]:
    developFromDir(getCurrentDir(), options)
  else:
    # Install each package.
    for pv in options.action.packages:
      let name =
        if isURL(pv.name):
          parseUri(pv.name).path.splitPath().tail
        else:
          pv.name
      let downloadDir = getCurrentDir() / name
      if dirExists(downloadDir):
        let msg = "Cannot clone into '$1': directory exists." % downloadDir
        let hint = "Remove the directory, or run this command somewhere else."
        raiseNimbleError(msg, hint)

      let (meth, url, metadata) = getDownloadInfo(pv, options, true)
      let subdir = metadata.getOrDefault("subdir")

      # Download the HEAD and make sure the full history is downloaded.
      let ver =
        if pv.ver.kind == verAny:
          parseVersionRange("#head")
        else:
          pv.ver
      var options = options
      options.forceFullClone = true
      discard downloadPkg(url, ver, meth, subdir, options, downloadDir)
      developFromDir(downloadDir / subdir, options)

proc test(options: Options) =
  ## Executes all tests starting with 't' in the ``tests`` directory.
  ## Subdirectories are not walked.
  var pkgInfo = getPkgInfo(getCurrentDir(), options)

  var
    files = toSeq(walkDir(getCurrentDir() / "tests"))
    tests, failures: int

  if files.len < 1:
    display("Warning:", "No tests found!", Warning, HighPriority)
    return

  if not execHook(options, actionCustom, true):
    raise newException(NimbleError, "Pre-hook prevented further execution.")

  files.sort((a, b) => cmp(a.path, b.path))

  for file in files:
    let (_, name, ext) = file.path.splitFile()
    if ext == ".nim" and name[0] == 't' and file.kind in {pcFile, pcLinkToFile}:
      var optsCopy = options.briefClone()
      optsCopy.action = Action(typ: actionCompile)
      optsCopy.action.file = file.path
      optsCopy.action.backend = pkgInfo.backend
      optsCopy.getCompilationFlags() = options.getCompilationFlags()
      # treat run flags as compile for default test task
      optsCopy.getCompilationFlags().add(options.action.custRunFlags)
      optsCopy.getCompilationFlags().add("-r")
      optsCopy.getCompilationFlags().add("--path:.")
      let
        binFileName = file.path.changeFileExt(ExeExt)
        existsBefore = fileExists(binFileName)

      if options.continueTestsOnFailure:
        inc tests
        try:
          execBackend(pkgInfo, optsCopy)
        except NimbleError:
          inc failures
      else:
        execBackend(pkgInfo, optsCopy)

      let
        existsAfter = fileExists(binFileName)
        canRemove = not existsBefore and existsAfter
      if canRemove:
        try:
          removeFile(binFileName)
        except OSError as exc:
          display("Warning:", "Failed to delete " & binFileName & ": " &
                  exc.msg, Warning, MediumPriority)

  if failures == 0:
    display("Success:", "All tests passed", Success, HighPriority)
  else:
    let error = "Only " & $(tests - failures) & "/" & $tests & " tests passed"
    display("Error:", error, Error, HighPriority)

  if not execHook(options, actionCustom, false):
    return

proc check(options: Options) =
  ## Validates a package in the current working directory.
  let nimbleFile = findNimbleFile(getCurrentDir(), true)
  var error: ValidationError
  var pkgInfo: PackageInfo
  var validationResult = false
  try:
    validationResult = validate(nimbleFile, options, error, pkgInfo)
  except:
    raiseNimbleError("Could not validate package:\n" & getCurrentExceptionMsg())

  if validationResult:
    display("Success:", pkgInfo.name & " is valid!", Success, HighPriority)
  else:
    display("Error:", error.msg, Error, HighPriority)
    display("Hint:", error.hint, Warning, HighPriority)
    display("Failure:", "Validation failed", Error, HighPriority)
    quit(QuitFailure)

proc run(options: Options) =
  # Verify parameters.
  var pkgInfo = getPkgInfo(getCurrentDir(), options)

  let binary = options.getCompilationBinary(pkgInfo).get("")
  if binary.len == 0:
    raiseNimbleError("Please specify a binary to run")

  if binary notin toSeq(pkgInfo.bin.keys):
    raiseNimbleError(
      "Binary '$#' is not defined in '$#' package." % [binary, pkgInfo.name]
    )

  # Build the binary.
  build(options)

  let binaryPath = pkgInfo.getOutputDir(binary)
  let cmd = quoteShellCommand(binaryPath & options.action.runFlags)
  displayDebug("Executing", cmd)
  cmd.execCmd.quit


proc doAction(options: var Options) =
  if options.showHelp:
    writeHelp()
  if options.showVersion:
    writeVersion()

  setNimBin(options)
  setNimbleDir(options)

  if options.action.typ in {actionTasks, actionRun, actionBuild, actionCompile}:
    # Implicitly disable package validation for these commands.
    options.disableValidation = true

  case options.action.typ
  of actionRefresh:
    refresh(options)
  of actionInstall:
    let
      pkgs = install(options.action.packages, options)
      pkgInfo = pkgs[^1]
    if options.action.packages.len == 0:
      nimScriptHint(pkgInfo)
    if pkgInfo.foreignDeps.len > 0:
      display("Hint:", "This package requires some external dependencies.",
              Warning, HighPriority)
      display("Hint:", "To install them you may be able to run:",
              Warning, HighPriority)
      for i in 0..<pkgInfo.foreignDeps.len:
        display("Hint:", "  " & pkgInfo.foreignDeps[i], Warning, HighPriority)
  of actionUninstall:
    uninstall(options)
  of actionSearch:
    search(options)
  of actionList:
    if options.queryInstalled: listInstalled(options)
    else: list(options)
  of actionPath:
    listPaths(options)
  of actionBuild:
    build(options)
  of actionRun:
    run(options)
  of actionCompile, actionDoc:
    var pkgInfo = getPkgInfo(getCurrentDir(), options)
    execBackend(pkgInfo, options)
  of actionInit:
    init(options)
  of actionPublish:
    var pkgInfo = getPkgInfo(getCurrentDir(), options)
    publish(pkgInfo, options)
  of actionDump:
    dump(options)
  of actionTasks:
    listTasks(options)
  of actionDevelop:
    develop(options)
  of actionCheck:
    check(options)
  of actionNil:
    assert false
  of actionCustom:
    let
      command = options.action.command.normalize
      nimbleFile = findNimbleFile(getCurrentDir(), true)
      pkgInfo = getPkgInfoFromFile(nimbleFile, options)

    if command in pkgInfo.nimbleTasks:
      # If valid task defined in nimscript, run it
      var execResult: ExecutionResult[bool]
      if execCustom(nimbleFile, options, execResult):
        if execResult.hasTaskRequestedCommand():
          var options = execResult.getOptionsForCommand(options)
          doAction(options)
    elif command == "test":
      # If there is no task defined for the `test` task, we run the pre-defined
      # fallback logic.
        test(options)
    else:
      raiseNimbleError(msg = "Could not find task $1 in $2" %
                            [options.action.command, nimbleFile],
                      hint = "Run `nimble --help` and/or `nimble tasks` for" &
                              " a list of possible commands.")

when isMainModule:
  var error = ""
  var hint = ""

  var opt: Options
  try:
    opt = parseCmdLine()
    opt.startDir = getCurrentDir()
    opt.doAction()
  except NimbleError:
    let currentExc = (ref NimbleError)(getCurrentException())
    (error, hint) = getOutputInfo(currentExc)
  except NimbleQuit:
    discard
  finally:
    try:
      let folder = getNimbleTempDir()
      if opt.shouldRemoveTmp(folder):
        removeDir(folder)
    except OSError:
      let msg = "Couldn't remove Nimble's temp dir"
      display("Warning:", msg, Warning, MediumPriority)

  if error.len > 0:
    displayTip()
    display("Error:", error, Error, HighPriority)
    if hint.len > 0:
      display("Hint:", hint, Warning, HighPriority)
    quit(1)
