[CmdletBinding()]
param(
    # Mutant names from the catalog. Empty: every mutant of the selected groups.
    [string[]]$Mutants = @(),

    # Catalog groups to run when -Mutants is empty. "hunt-controls" (seven mutants the corpora
    # already killed during the 2026-11-20 hunt) is left out by default to keep the pilot short.
    [string[]]$Groups = @("hunt-gaps", "extension"),

    # The mutant catalog (scripts/lean-model-mutants.psd1).
    [string]$Catalog = "",

    # Parent for a fresh, run-private Lake workspace. Defaults to the system temporary directory.
    [string]$Workspace = "",

    # Take the four corpus modules (and their support module) from this commit instead of the working
    # tree, against the working tree's model: what an earlier corpus made of a mutant. The catalog's
    # `Expect` describes the current corpora, so it is not enforced for such a run.
    [string]$CorpusRevision = "",

    # Additional Lean modules of `#guard`s (each imports KatLang) elaborated against the baseline and
    # every mutant, and reported apart from the corpora: candidate witnesses for a surviving mutant.
    [string[]]$ControlModules = @(),

    # A mutant step (a build or one corpus) is stopped after max(MinimumTimeoutSeconds,
    # TimeoutFactor x the same step's baseline time in this run). The baseline itself has no
    # deadline. A wrong decision can make the model loop on a corpus program, so a mutant needs one.
    [ValidateRange(2, 100)]
    [int]$TimeoutFactor = 6,

    [ValidateRange(30, 86400)]
    [int]$MinimumTimeoutSeconds = 240,

    # Check the catalog's anchors against lean/KatLang.lean and stop: no workspace, no build.
    [switch]$CheckCatalog
)

# The on-demand Lean-model mutation campaign (docs/design/lean-model-mutation-campaign-2026-11.md).
# It asks whether the generated Lean/C# differential corpora notice a wrong decision in the Lean
# model: it copies lean/KatLang.lean and the four corpus modules into a scratch Lake workspace
# OUTSIDE the tracked tree, checks that the unmodified copy passes every `#guard` (the baseline),
# and then, ONE MUTANT AT A TIME, rewrites the copy of the model with one catalogued substitution,
# builds it and elaborates the corpora against it. A mutant is
#   Killed        at least one `#guard` of a corpus fails (the failing guards name the cases);
#   Survived      every corpus elaborates cleanly: no committed guard notices the change;
#   Invalid       an anchor does not match exactly once, the substitution changes nothing, or the
#                 mutated model does not build;
#   TimedOut      a step exceeded its deadline and no guard had failed (never counted as a kill:
#                 a loop the mutant causes and a slow machine look the same from here);
#   Inconclusive  no guard failed, and a corpus reported other errors or Lean ended abnormally
#                 (a mutant that recurses without bound ends in the interpreter's deep-recursion
#                 abort, which loses the rest of that module).
# A corpus that was stopped at its deadline or aborted keeps the guard failures it reported before
# that, so such a mutant is still Killed, with that corpus marked as partial.
# The tracked files are read, never written: the run fingerprints the repository and the copied
# inputs before and after and fails if either changed. Every log and the results go to a fresh
# git-ignored artifacts/validation/lean-model-mutants-* directory (a temporary directory if that
# path is not ignored). It fails when the baseline is not clean, when a mutant is Invalid, TimedOut
# or Inconclusive, or when a verdict disagrees with the catalog's `Expect`. It is not a validation
# level, runs no .NET test, and does not change the `validate-all.ps1` phase contract.

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path

# A relative -Catalog, -Workspace or -ControlModules path is the caller's, not the repository's.
$callerDirectory = (Get-Location).ProviderPath
$Catalog = if ([string]::IsNullOrWhiteSpace($Catalog)) {
    Join-Path $PSScriptRoot "lean-model-mutants.psd1"
}
else {
    [System.IO.Path]::GetFullPath($Catalog, $callerDirectory)
}

# The four generated corpora, in report order, and the modules they import besides the model.
$corpora = @(
    [pscustomobject]@{ Name = "LanguageSpec"; Path = "LanguageSpecCases.lean" },
    [pscustomobject]@{ Name = "SemanticExplorer"; Path = "SemanticExplorerCases.lean" },
    [pscustomobject]@{ Name = "SEM-2C"; Path = "CoreTests/SemanticGeneratedCases.lean" },
    [pscustomobject]@{ Name = "HostParent"; Path = "CoreTests/HostParentDifferential.lean" }
)
$supportModules = @("CoreTests/StructuralIdentity.lean")
$workspaceConfiguration = @("lakefile.lean", "lake-manifest.json", "lean-toolchain")
$modelPath = "KatLang.lean"
$buildTargets = @("KatLang", "CoreTests.StructuralIdentity")
$maximumLogCharacters = 400000
$maximumErrors = 100000

function Get-TextDigest {
    param([AllowEmptyString()][Parameter(Mandatory = $true)][string]$Text)

    $bytes = [System.Text.Encoding]::UTF8.GetBytes($Text)
    return [System.Convert]::ToHexString([System.Security.Cryptography.SHA256]::HashData($bytes))
}

function Invoke-Git {
    param([Parameter(Mandatory = $true)][string[]]$Arguments)

    # An array, so a command without output yields no element (never one null element).
    $output = @(& git @Arguments)
    if ($LASTEXITCODE -ne 0) {
        throw "git $($Arguments -join ' ') failed with exit code $LASTEXITCODE"
    }

    return $output
}

function Get-RepositorySnapshot {
    # The same four parts as validate-all.ps1: the porcelain status alone would miss a rewrite of a
    # file that was already modified when the run began.
    $status = (Invoke-Git @("status", "--porcelain=v1", "--untracked-files=all")) -join "`n"
    $indexDiff = (Invoke-Git @("diff", "--cached", "--binary", "--no-ext-diff", "--no-textconv", "--")) -join "`n"
    $worktreeDiff = (Invoke-Git @("diff", "--binary", "--no-ext-diff", "--no-textconv", "--")) -join "`n"
    $untracked = [System.Collections.Generic.List[string]]::new()
    foreach ($path in @(Invoke-Git @("ls-files", "--others", "--exclude-standard")) | Sort-Object) {
        $untracked.Add("$path`0$((Invoke-Git @('hash-object', '--no-filters', '--', $path)) -join '')")
    }

    return [pscustomobject]@{
        Head = (Invoke-Git @("rev-parse", "HEAD")) -join ""
        Status = $status
        IndexDigest = Get-TextDigest -Text $indexDiff
        WorktreeDigest = Get-TextDigest -Text $worktreeDiff
        UntrackedDigest = Get-TextDigest -Text ($untracked -join "`n")
    }
}

function Test-SameSnapshot {
    param([Parameter(Mandatory = $true)]$Before, [Parameter(Mandatory = $true)]$After)

    return $Before.Head -ceq $After.Head `
        -and $Before.Status -ceq $After.Status `
        -and $Before.IndexDigest -ceq $After.IndexDigest `
        -and $Before.WorktreeDigest -ceq $After.WorktreeDigest `
        -and $Before.UntrackedDigest -ceq $After.UntrackedDigest
}

function Get-InputDigests {
    param([Parameter(Mandatory = $true)][string[]]$RelativePaths, [string]$Directory = (Join-Path $repoRoot "lean"))

    $digests = [ordered]@{}
    foreach ($relative in $RelativePaths) {
        $digests[$relative] = (Get-FileHash -LiteralPath (Join-Path $Directory $relative) -Algorithm SHA256).Hash
    }

    return $digests
}

# Writes one file of a commit to a path, byte for byte.
function Save-CommittedFile {
    param(
        [Parameter(Mandatory = $true)][string]$Commit,
        [Parameter(Mandatory = $true)][string]$RepositoryPath,
        [Parameter(Mandatory = $true)][string]$Destination
    )

    $info = [System.Diagnostics.ProcessStartInfo]::new("git")
    foreach ($argument in @("cat-file", "blob", "${Commit}:$RepositoryPath")) {
        $info.ArgumentList.Add($argument)
    }

    $info.WorkingDirectory = $repoRoot
    $info.UseShellExecute = $false
    $info.RedirectStandardOutput = $true
    $info.RedirectStandardError = $true
    $process = [System.Diagnostics.Process]::Start($info)
    try {
        $errors = $process.StandardError.ReadToEndAsync()
        $stream = [System.IO.File]::Create($Destination)
        try {
            $process.StandardOutput.BaseStream.CopyTo($stream)
        }
        finally {
            $stream.Dispose()
        }

        $process.WaitForExit()
        if ($process.ExitCode -ne 0) {
            throw "git cat-file blob ${Commit}:$RepositoryPath failed: $($errors.GetAwaiter().GetResult().Trim())"
        }
    }
    finally {
        $process.Dispose()
    }
}

function Initialize-Diagnostics {
    # A fresh directory under artifacts/validation/ once git confirms it is ignored, otherwise an
    # external temporary directory. Nothing existing is overwritten or deleted.
    $name = "lean-model-mutants-{0:yyyyMMddTHHmmssZ}-{1}" -f [DateTime]::UtcNow, $PID
    $relative = "artifacts/validation/$name"
    & git check-ignore -q -- "$relative/results.json"
    $directory = if ($LASTEXITCODE -eq 0) {
        Join-Path $repoRoot $relative
    }
    else {
        Join-Path ([System.IO.Path]::GetTempPath()) "katlang-$name"
    }

    New-Item -ItemType Directory -Force -Path $directory | Out-Null
    return $directory
}

function Resolve-Workspace {
    $path = if ([string]::IsNullOrWhiteSpace($Workspace)) {
        [System.IO.Path]::GetTempPath()
    }
    else {
        $Workspace
    }

    $parent = [System.IO.Path]::GetFullPath($path, $callerDirectory)
    $full = Join-Path $parent ("katlang-mutants-" + [guid]::NewGuid().ToString("N"))
    $rootWithSeparator = $repoRoot.TrimEnd([System.IO.Path]::DirectorySeparatorChar, [System.IO.Path]::AltDirectorySeparatorChar) + [System.IO.Path]::DirectorySeparatorChar
    $comparison = if ($IsWindows) { [System.StringComparison]::OrdinalIgnoreCase } else { [System.StringComparison]::Ordinal }
    if ($full.Equals($repoRoot, $comparison) -or $full.StartsWith($rootWithSeparator, $comparison)) {
        # Inside the checkout only where git ignores it: a mutated model must never be a candidate file.
        & git check-ignore -q -- (Join-Path $full "KatLang.lean")
        if ($LASTEXITCODE -ne 0) {
            throw "the workspace '$full' is inside the repository and not git-ignored; the mutated model must stay out of the tracked tree"
        }
    }

    # Never reuse someone else's inputs, symlinks or Lake cache, even for two runs with one parent.
    New-Item -ItemType Directory -Path $full -ErrorAction Stop | Out-Null
    # Git resolves the working directory physically, including junctions leading into a checkout.
    $inside = & git -C $full rev-parse --is-inside-work-tree 2>$null
    if ($LASTEXITCODE -eq 0 -and $inside -eq "true") {
        & git -C $full check-ignore -q -- KatLang.lean
        if ($LASTEXITCODE -ne 0) { throw "the scratch directory '$full' is in an unignored worktree" }
    }
    return $full
}

function ConvertTo-Lf {
    param([AllowEmptyString()][Parameter(Mandatory = $true)][string]$Text)

    return $Text.Replace("`r`n", "`n")
}

function Get-OccurrenceCount {
    param([Parameter(Mandatory = $true)][string]$Text, [Parameter(Mandatory = $true)][string]$Fragment)

    $count = 0
    $index = $Text.IndexOf($Fragment, [System.StringComparison]::Ordinal)
    while ($index -ge 0) {
        $count++
        $index = $Text.IndexOf($Fragment, $index + 1, [System.StringComparison]::Ordinal)
    }

    return $count
}

# Applies a mutant's substitutions to the model text. Returns the mutated text, or the reason the
# mutant is invalid: every anchor must match exactly once and the result must differ from the model.
function Get-MutatedModel {
    param([Parameter(Mandatory = $true)][string]$Model, [Parameter(Mandatory = $true)]$Mutant)

    $text = $Model
    $sites = [System.Collections.Generic.List[int]]::new()
    $number = 0
    foreach ($edit in @($Mutant.Edits)) {
        $number++
        $find = ConvertTo-Lf -Text ([string]$edit.Find)
        $replace = ConvertTo-Lf -Text ([string]$edit.Replace)
        if ($find.Length -eq 0) {
            return [pscustomobject]@{ Text = $null; Problem = "edit $number has an empty anchor"; Lines = @() }
        }

        $count = Get-OccurrenceCount -Text $text -Fragment $find
        if ($count -ne 1) {
            return [pscustomobject]@{ Text = $null; Problem = "the anchor of edit $number matches $count times (exactly 1 required)"; Lines = @() }
        }

        $index = $text.IndexOf($find, [System.StringComparison]::Ordinal)
        $sites.Add(($text.Substring(0, $index).Split("`n").Length))
        $text = $text.Substring(0, $index) + $replace + $text.Substring($index + $find.Length)
    }

    if ($text -ceq $Model) {
        return [pscustomobject]@{ Text = $null; Problem = "the substitutions leave the model unchanged"; Lines = @($sites) }
    }

    return [pscustomobject]@{ Text = $text; Problem = $null; Lines = @($sites) }
}

# Runs `lake` in the workspace with its whole output captured to a log. A positive deadline stops the
# process tree when it passes; the exit code is then null and TimedOut is set.
function Invoke-Lake {
    param(
        [Parameter(Mandatory = $true)][string[]]$Arguments,
        [Parameter(Mandatory = $true)][string]$WorkingDirectory,
        [Parameter(Mandatory = $true)][string]$Log,
        [int]$TimeoutSeconds = 0
    )

    $info = [System.Diagnostics.ProcessStartInfo]::new("lake")
    foreach ($argument in $Arguments) {
        $info.ArgumentList.Add($argument)
    }

    $info.WorkingDirectory = $WorkingDirectory
    $info.UseShellExecute = $false
    $info.RedirectStandardOutput = $true
    $info.RedirectStandardError = $true
    $info.StandardOutputEncoding = [System.Text.Encoding]::UTF8
    $info.StandardErrorEncoding = [System.Text.Encoding]::UTF8

    $watch = [System.Diagnostics.Stopwatch]::StartNew()
    $process = [System.Diagnostics.Process]::Start($info)
    try {
        $standardOutput = $process.StandardOutput.ReadToEndAsync()
        $standardError = $process.StandardError.ReadToEndAsync()
        $timedOut = $false
        if ($TimeoutSeconds -gt 0) {
            if (-not $process.WaitForExit([TimeSpan]::FromSeconds($TimeoutSeconds))) {
                $timedOut = $true
                try { $process.Kill($true) } catch { }
            }
        }

        $process.WaitForExit()
        $text = $standardOutput.GetAwaiter().GetResult() + $standardError.GetAwaiter().GetResult()
        $exitCode = if ($timedOut) { $null } else { $process.ExitCode }
    }
    finally {
        $process.Dispose()
    }

    # An aborting Lean process can print a stack trace of tens of megabytes: the log keeps both ends.
    $logged = if ($text.Length -gt $maximumLogCharacters) {
        $half = [int]($maximumLogCharacters / 2)
        $text.Substring(0, $half) + "`n... [$($text.Length - $maximumLogCharacters) characters omitted] ...`n" + $text.Substring($text.Length - $half)
    }
    else {
        $text
    }

    [System.IO.File]::WriteAllText($Log, $logged, [System.Text.UTF8Encoding]::new($false))
    return [pscustomobject]@{
        ExitCode = $exitCode
        TimedOut = $timedOut
        Seconds = [Math]::Round($watch.Elapsed.TotalSeconds, 1)
        Output = $text
    }
}

# The case a guard line belongs to: the nearest comment line above it (every generated case block
# starts with `-- <id> ...`), reduced to the id and, for a member of a case, its bracketed role.
function Get-GuardCase {
    param([Parameter(Mandatory = $true)][AllowEmptyString()][string[]]$Lines, [Parameter(Mandatory = $true)][int]$LineNumber)

    for ($index = $LineNumber - 2; $index -ge 0; $index--) {
        $line = $Lines[$index]
        if ($line.StartsWith("-- ", [System.StringComparison]::Ordinal)) {
            $match = [regex]::Match($line, '^-- (?<id>\S+?)(?::|\s|$)(?:\s*(?<role>\[[^\]]+\]))?')
            if ($match.Success) {
                $role = if ($match.Groups["role"].Success -and $line -notmatch '^-- \S+ \[[^\]]+\]:') { " " + $match.Groups["role"].Value } else { "" }
                return $match.Groups["id"].Value + $role
            }

            return $line.Substring(3).Trim()
        }
    }

    return "(line $LineNumber)"
}

# Elaborates one module of the workspace against the built model and reads its errors: an error on a
# `#guard` line whose message is the failed-guard message is a failing guard; every other error is kept
# apart, because it is not evidence that a guard noticed the mutant.
function Invoke-Module {
    param(
        [Parameter(Mandatory = $true)][string]$RelativePath,
        [Parameter(Mandatory = $true)][string]$WorkspaceDirectory,
        [Parameter(Mandatory = $true)][string]$Log,
        [int]$TimeoutSeconds = 0
    )

    # Lean stops a module at 100 errors by default; a mutant can fail more guards than that.
    $run = Invoke-Lake -Arguments @("env", "lean", "-DmaxErrors=$maximumErrors", $RelativePath) -WorkingDirectory $WorkspaceDirectory -Log $Log -TimeoutSeconds $TimeoutSeconds
    $sourceLines = [System.IO.File]::ReadAllText((Join-Path $WorkspaceDirectory $RelativePath)).Replace("`r`n", "`n").Split("`n")
    $outputLines = $run.Output.Replace("`r`n", "`n").Split("`n")
    $guards = [System.Collections.Generic.List[object]]::new()
    $others = [System.Collections.Generic.List[object]]::new()
    for ($index = 0; $index -lt $outputLines.Length; $index++) {
        $match = [regex]::Match($outputLines[$index], '^(?<file>.+?):(?<line>\d+):(?<column>\d+): error(?:\([^)]*\))?: ?(?<message>.*)$')
        if (-not $match.Success) {
            continue
        }

        $lineNumber = [int]$match.Groups["line"].Value
        $source = if ($lineNumber -ge 1 -and $lineNumber -le $sourceLines.Length) { $sourceLines[$lineNumber - 1] } else { "" }
        $message = $match.Groups["message"].Value.Trim()
        $guardDiagnostic = $false
        if ($message -ceq "Expression") {
            for ($next = $index + 1; $next -lt $outputLines.Length; $next++) {
                if ($outputLines[$next].StartsWith("  ", [System.StringComparison]::Ordinal)) { continue }
                $guardDiagnostic = $outputLines[$next] -ceq 'did not evaluate to `true`'
                break
            }
        }
        $isGuard = $guardDiagnostic -and ($match.Groups["file"].Value.Replace('\', '/') -ceq $RelativePath) -and
            $source -cmatch '^#guard\s'
        if ($isGuard) {
            $guards.Add([pscustomobject]@{
                Line = $lineNumber
                Case = Get-GuardCase -Lines $sourceLines -LineNumber $lineNumber
                Guard = if ($source.Length -gt 240) { $source.Substring(0, 240) + "..." } else { $source }
            })
        }
        else {
            $detail = if ($message.Length -gt 0) { $message } elseif ($index + 1 -lt $outputLines.Length) { $outputLines[$index + 1].Trim() } else { "" }
            $others.Add([pscustomobject]@{ Line = $lineNumber; Message = if ($detail.Length -gt 240) { $detail.Substring(0, 240) + "..." } else { $detail } })
        }
    }

    # Lean ended abnormally without reporting an error at a source position: the interpreter's
    # deep-recursion abort, a crash, or a missing tool. The module's remaining guards never ran.
    $aborted = -not $run.TimedOut -and $run.ExitCode -ne 0 -and ($guards.Count + $others.Count) -eq 0
    $abortedPartial = -not $run.TimedOut -and $run.Output.Contains("deep recursion was detected", [System.StringComparison]::Ordinal)
    $state = if ($others.Count -gt 0) { "OtherErrors" }
        elseif ($guards.Count -gt 0) { "GuardsFailed" }
        elseif ($run.TimedOut) { "TimedOut" }
        elseif ($aborted -or $abortedPartial) { "Aborted" }
        else { "Clean" }
    $firstLine = @($outputLines | Where-Object { $_.Trim().Length -gt 0 } | Select-Object -First 1)

    return [pscustomobject]@{
        Module = $RelativePath
        State = $state
        TimedOut = $run.TimedOut
        Aborted = [bool]($aborted -or $abortedPartial)
        AbortMessage = if (($aborted -or $abortedPartial) -and $firstLine.Count -gt 0) { $firstLine[0].Substring(0, [Math]::Min(200, $firstLine[0].Length)) } else { "" }
        ExitCode = $run.ExitCode
        Seconds = $run.Seconds
        GuardCommands = @($sourceLines -cmatch '^#guard\s').Count
        FailingGuards = $guards.Count
        FailingCases = @($guards | ForEach-Object { $_.Case } | Select-Object -Unique)
        Guards = @($guards)
        OtherErrors = @($others)
        Log = [System.IO.Path]::GetFileName($Log)
    }
}

function Get-Deadline {
    param([double]$BaselineSeconds)

    return [int][Math]::Max($MinimumTimeoutSeconds, [Math]::Ceiling($BaselineSeconds * $TimeoutFactor))
}

# One mutant (or the baseline, with the unmodified model text) through the build and the modules.
function Invoke-Candidate {
    param(
        [Parameter(Mandatory = $true)][string]$Name,
        [Parameter(Mandatory = $true)][string]$ModelText,
        [Parameter(Mandatory = $true)][string]$WorkspaceDirectory,
        [Parameter(Mandatory = $true)][string]$Diagnostics,
        [Parameter(Mandatory = $true)][AllowEmptyCollection()][string[]]$ControlPaths,
        $Baseline = $null
    )

    [System.IO.File]::WriteAllText((Join-Path $WorkspaceDirectory $modelPath), $ModelText, [System.Text.UTF8Encoding]::new($false))
    $buildDeadline = if ($null -eq $Baseline) { 0 } else { Get-Deadline -BaselineSeconds $Baseline.Build.Seconds }
    $buildLog = Join-Path $Diagnostics "$Name-build.log"
    $build = Invoke-Lake -Arguments (@("build") + $buildTargets) -WorkingDirectory $WorkspaceDirectory -Log $buildLog -TimeoutSeconds $buildDeadline
    $result = [ordered]@{
        Name = $Name
        Build = [pscustomobject]@{ ExitCode = $build.ExitCode; TimedOut = $build.TimedOut; Seconds = $build.Seconds; Log = [System.IO.Path]::GetFileName($buildLog) }
        Corpora = @()
        Controls = @()
    }
    if ($build.TimedOut -or $build.ExitCode -ne 0) {
        return [pscustomobject]$result
    }

    $corpusResults = [System.Collections.Generic.List[object]]::new()
    foreach ($corpus in $corpora) {
        $deadline = if ($null -eq $Baseline) { 0 } else {
            Get-Deadline -BaselineSeconds (@($Baseline.Corpora | Where-Object { $_.Module -ceq $corpus.Path })[0].Seconds)
        }
        $outcome = Invoke-Module -RelativePath $corpus.Path -WorkspaceDirectory $WorkspaceDirectory `
            -Log (Join-Path $Diagnostics "$Name-$($corpus.Name).log") -TimeoutSeconds $deadline
        $outcome | Add-Member -NotePropertyName Corpus -NotePropertyValue $corpus.Name
        $corpusResults.Add($outcome)
    }

    $controlResults = [System.Collections.Generic.List[object]]::new()
    foreach ($control in $ControlPaths) {
        $deadline = if ($null -eq $Baseline) { 0 } else {
            Get-Deadline -BaselineSeconds (@($Baseline.Controls | Where-Object { $_.Module -ceq $control })[0].Seconds)
        }
        $label = [System.IO.Path]::GetFileNameWithoutExtension($control)
        $outcome = Invoke-Module -RelativePath $control -WorkspaceDirectory $WorkspaceDirectory `
            -Log (Join-Path $Diagnostics "$Name-control-$label.log") -TimeoutSeconds $deadline
        $outcome | Add-Member -NotePropertyName Corpus -NotePropertyValue "control:$label"
        $controlResults.Add($outcome)
    }

    $result.Corpora = @($corpusResults)
    $result.Controls = @($controlResults)
    return [pscustomobject]$result
}

# The verdict of one mutant from its build and corpus outcomes (controls never decide it).
function Get-Verdict {
    param([Parameter(Mandatory = $true)]$Run)

    if ($Run.Build.TimedOut) { return "TimedOut" }
    if ($Run.Build.ExitCode -ne 0) { return "Invalid" }
    $states = @($Run.Corpora | ForEach-Object { $_.State })
    if ($states -contains "GuardsFailed") { return "Killed" }
    if ($states -contains "TimedOut") { return "TimedOut" }
    if ($states -contains "OtherErrors" -or $states -contains "Aborted") { return "Inconclusive" }
    return "Survived"
}

Push-Location $repoRoot
try {
    # An inherited regeneration flag must never reach a child of this run.
    $regenerationFlags = @(Get-ChildItem Env: | Where-Object { $_.Name -like "KATLANG_REGENERATE_*" })
    foreach ($variable in $regenerationFlags) {
        Remove-Item -LiteralPath "Env:$($variable.Name)"
    }

    $catalogData = Import-PowerShellDataFile -LiteralPath $Catalog
    $all = @($catalogData.Mutants)
    $names = @($all | ForEach-Object { [string]$_.Name })
    if (@($names | Select-Object -Unique).Count -ne $names.Count) {
        throw "the catalog has duplicate mutant names"
    }

    foreach ($entry in $all) {
        if ([string]$entry.Name -cnotmatch '^[a-z0-9][a-z0-9-]*$' -or $entry.Name -ceq "baseline") {
            throw "the mutant name '$($entry.Name)' must be lower-case letters, digits and hyphens"
        }

        if (@("", "Killed", "Survives") -cnotcontains [string]$entry.Expect) {
            throw "mutant '$($entry.Name)': Expect must be Killed, Survives or empty"
        }
    }

    # `pwsh -File` passes `a,b` as ONE string, so a comma-separated value is split here.
    $requestedMutants = @($Mutants | ForEach-Object { $_ -split "," } | ForEach-Object { $_.Trim() } | Where-Object { $_ })
    $requestedGroups = @($Groups | ForEach-Object { $_ -split "," } | ForEach-Object { $_.Trim() } | Where-Object { $_ })
    foreach ($name in $requestedMutants) {
        if ($names -cnotcontains $name) {
            throw "unknown mutant '$name' (catalog: $($names -join ', '))"
        }
    }

    $knownGroups = @($all | ForEach-Object { [string]$_.Group } | Select-Object -Unique)
    foreach ($group in $requestedGroups) {
        if ($knownGroups -cnotcontains $group) {
            throw "unknown group '$group' (catalog: $($knownGroups -join ', '))"
        }
    }

    $selected = @(if ($requestedMutants.Count -gt 0) {
        $all | Where-Object { $requestedMutants -ccontains [string]$_.Name }
    }
    else {
        $all | Where-Object { $requestedGroups -ccontains [string]$_.Group }
    })

    if ($selected.Count -eq 0) {
        throw "no mutant selected (groups: $($requestedGroups -join ', '))"
    }

    $model = ConvertTo-Lf -Text ([System.IO.File]::ReadAllText((Join-Path $repoRoot "lean/$modelPath")))
    $prepared = [ordered]@{}
    foreach ($entry in $selected) {
        $prepared[[string]$entry.Name] = Get-MutatedModel -Model $model -Mutant $entry
    }

    if ($CheckCatalog) {
        $stale = 0
        foreach ($entry in $selected) {
            $mutation = $prepared[[string]$entry.Name]
            if ($null -ne $mutation.Problem) {
                $stale++
                Write-Host ("{0,-34} INVALID  {1}" -f $entry.Name, $mutation.Problem)
            }
            else {
                Write-Host ("{0,-34} ok       {1}  line {2}" -f $entry.Name, $entry.Group, ($mutation.Lines -join ", "))
            }
        }

        if ($stale -gt 0) {
            throw "$stale mutant(s) do not apply to lean/$modelPath"
        }

        return
    }

    $controlSources = @((Join-Path $PSScriptRoot "LeanMutationWitnesses.lean"))
    foreach ($control in @($ControlModules | ForEach-Object { $_ -split "," } | ForEach-Object { $_.Trim() } | Where-Object { $_ })) {
        $source = [System.IO.Path]::GetFullPath($control, $callerDirectory)
        if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
            throw "control module not found: $source"
        }

        if ([System.IO.Path]::GetFileName($source) -notmatch '^[A-Za-z0-9_]+\.lean$') {
            throw "a control module needs a plain Lean file name (letters, digits, underscore): $source"
        }

        if ([System.IO.Path]::GetFileName($source) -in @($controlSources | ForEach-Object { [System.IO.Path]::GetFileName($_) })) {
            throw "duplicate control module filename: $source"
        }
        $controlSources += $source
    }

    $corpusCommit = ""
    if (-not [string]::IsNullOrWhiteSpace($CorpusRevision)) {
        $corpusCommit = (Invoke-Git @("rev-parse", "--verify", "--quiet", "$CorpusRevision^{commit}")) -join ""
    }

    $workspaceDirectory = Resolve-Workspace
    $diagnostics = Initialize-Diagnostics
    $record = Join-Path $diagnostics "lean-model-mutants.log"
    $inputPaths = @($modelPath) + @($corpora | ForEach-Object { $_.Path }) + $supportModules + $workspaceConfiguration
    $snapshotBefore = Get-RepositorySnapshot
    $digestsBefore = Get-InputDigests -RelativePaths $inputPaths
    "lean-model mutants: head=$($snapshotBefore.Head) corpora=$(if ($corpusCommit) { $corpusCommit } else { 'working tree' }) mutants=$(@($selected | ForEach-Object { $_.Name }) -join ',') workspace=$workspaceDirectory timeout-factor=$TimeoutFactor minimum-timeout=$MinimumTimeoutSeconds" |
        Set-Content -LiteralPath $record
    Write-Host "Lean-model mutant diagnostics: $diagnostics"
    Write-Host "Scratch workspace: $workspaceDirectory"

    # The fixture: copies of the configuration, the corpora and their support module. The model's
    # copy is written per candidate. Only steps within this run share the fixture's Lake cache.
    New-Item -ItemType Directory -Force -Path (Join-Path $workspaceDirectory "CoreTests") | Out-Null
    $fromCommit = if ($corpusCommit) { @($corpora | ForEach-Object { $_.Path }) + $supportModules } else { @() }
    foreach ($relative in @($inputPaths | Where-Object { $_ -cne $modelPath })) {
        if ($fromCommit -ccontains $relative) {
            Save-CommittedFile -Commit $corpusCommit -RepositoryPath "lean/$relative" -Destination (Join-Path $workspaceDirectory $relative)
        }
        else {
            Copy-Item -LiteralPath (Join-Path $repoRoot "lean/$relative") -Destination (Join-Path $workspaceDirectory $relative) -Force
        }
    }

    $controlPaths = @()
    if ($controlSources.Count -gt 0) {
        New-Item -ItemType Directory -Force -Path (Join-Path $workspaceDirectory "Controls") | Out-Null
        foreach ($source in $controlSources) {
            $relative = "Controls/" + [System.IO.Path]::GetFileName($source)
            Copy-Item -LiteralPath $source -Destination (Join-Path $workspaceDirectory $relative) -Force
            $controlPaths += $relative
        }
    }

    $fixtureDigests = Get-InputDigests -Directory $workspaceDirectory -RelativePaths (@($inputPaths | Where-Object { $_ -ne $modelPath }) + $controlPaths)
    $fixtureDigests[$modelPath] = Get-TextDigest -Text $model
    $clock = [System.Diagnostics.Stopwatch]::StartNew()
    $baseline = Invoke-Candidate -Name "baseline" -ModelText $model -WorkspaceDirectory $workspaceDirectory `
        -Diagnostics $diagnostics -ControlPaths $controlPaths
    $baselineSeconds = [Math]::Round($clock.Elapsed.TotalSeconds)
    $baselineProblems = @()
    if ($baseline.Build.ExitCode -ne 0) {
        $baselineProblems += "the unmodified model did not build (exit $($baseline.Build.ExitCode))"
    }

    foreach ($outcome in @($baseline.Corpora) + @($baseline.Controls)) {
        if ($outcome.GuardCommands -eq 0) {
            $baselineProblems += "$($outcome.Corpus): no guard commands"
        }
        if ($outcome.State -cne "Clean") {
            $baselineProblems += "$($outcome.Corpus): $($outcome.State) ($($outcome.FailingGuards) failing guards, $(@($outcome.OtherErrors).Count) other errors, exit $($outcome.ExitCode))"
        }
    }

    "baseline: build=$($baseline.Build.Seconds)s " + ((@($baseline.Corpora) + @($baseline.Controls) | ForEach-Object { "$($_.Corpus)=$($_.State)/$($_.Seconds)s" }) -join " ") + " total=${baselineSeconds}s" |
        Add-Content -LiteralPath $record

    $results = [System.Collections.Generic.List[object]]::new()
    if ($baselineProblems.Count -eq 0) {
        foreach ($entry in $selected) {
            $name = [string]$entry.Name
            $mutation = $prepared[$name]
            $clock.Restart()
            $expect = [string]$entry.Expect
            $required = if ($entry.ContainsKey("RequiredKillers")) { @($entry.RequiredKillers) } else { @() }
            $gap = if ($entry.ContainsKey("Gap")) { [string]$entry.Gap } else { "" }
            if ($null -ne $mutation.Problem) {
                $summary = [pscustomobject]@{
                    Name = $name; Group = [string]$entry.Group; Verdict = "Invalid"; Reason = $mutation.Problem
                    Expect = $expect; Gap = $gap; ModelLines = @(); Seconds = 0; Build = $null; Corpora = @(); Controls = @()
                    KillingCases = @(); MissingRequiredKillers = $required; MeetsExpectation = $false
                }
            }
            else {
                $run = Invoke-Candidate -Name $name -ModelText $mutation.Text -WorkspaceDirectory $workspaceDirectory `
                    -Diagnostics $diagnostics -ControlPaths $controlPaths -Baseline $baseline
                $verdict = Get-Verdict -Run $run
                $attributed = @($run.Corpora | Where-Object State -ceq "GuardsFailed")
                $killing = @($attributed | ForEach-Object { $corpus = $_.Corpus; $_.FailingCases | ForEach-Object { "${corpus}: $_" } })
                $caseIds = @($attributed | ForEach-Object { $_.FailingCases })
                $missing = @($required | Where-Object { $caseIds -cnotcontains $_ })
                $stopped = @($run.Corpora | Where-Object { $_.TimedOut } | ForEach-Object { $_.Corpus })
                $aborted = @($run.Corpora | Where-Object { $_.Aborted } | ForEach-Object { $_.Corpus })
                $partial = @()
                $otherErrors = @($run.Corpora | Where-Object State -ceq "OtherErrors" | ForEach-Object { $_.Corpus })
                if ($otherErrors.Count -gt 0) { $partial += "other elaboration errors: $($otherErrors -join ', ')" }
                if ($stopped.Count -gt 0) { $partial += "stopped at its deadline: $($stopped -join ', ')" }
                if ($aborted.Count -gt 0) { $partial += "Lean aborted: $($aborted -join ', ')" }
                $reason = switch ($verdict) {
                    "Invalid" { "the mutated model does not build (exit $($run.Build.ExitCode))" }
                    "TimedOut" { if ($run.Build.TimedOut) { "the build exceeded its deadline" } else { $partial -join "; " } }
                    "Inconclusive" { if ($partial.Count -gt 0) { $partial -join "; " } else { "errors that are not guard failures" } }
                    "Killed" { if ($partial.Count -gt 0) { "partial guard list, " + ($partial -join "; ") } else { "" } }
                    default { "" }
                }
                if ($corpusCommit) { $expect = "" }
                $meets = switch ($expect) {
                    "Killed" { $verdict -ceq "Killed" -and $missing.Count -eq 0 }
                    "Survives" { $verdict -ceq "Survived" }
                    default { $verdict -ceq "Killed" -or $verdict -ceq "Survived" }
                }
                if ($entry.ContainsKey("Witnesses")) {
                    $witnessCases = @($run.Controls | Where-Object Corpus -ceq "control:LeanMutationWitnesses" | ForEach-Object { $_.FailingCases })
                    $absent = @($entry.Witnesses | Where-Object { $witnessCases -cnotcontains $_ })
                    if ($absent.Count -gt 0) {
                        $reason = "$reason missing control failures: $($absent -join ', ')".Trim()
                        $meets = $false
                    }
                }
                foreach ($control in $run.Controls) {
                    if ($control.TimedOut -or $control.Aborted -or $control.State -ceq "OtherErrors") {
                        $reason = "$reason incomplete control: $($control.Module) ($($control.State))".Trim()
                        $meets = $false
                    }
                }
                $summary = [pscustomobject]@{
                    Name = $name; Group = [string]$entry.Group; Verdict = $verdict; Reason = $reason
                    Expect = $expect; Gap = $gap; ModelLines = @($mutation.Lines); Seconds = [Math]::Round($clock.Elapsed.TotalSeconds)
                    Build = $run.Build; Corpora = @($run.Corpora); Controls = @($run.Controls)
                    KillingCases = $killing; MissingRequiredKillers = $missing; MeetsExpectation = [bool]$meets
                }
            }

            $results.Add($summary)
            $counts = (@($summary.Corpora) | ForEach-Object { "$($_.Corpus)=$($_.FailingGuards)" }) -join " "
            $line = "${name}: verdict=$($summary.Verdict) expect=$(if ($expect) { $expect } else { '-' }) meets=$($summary.MeetsExpectation) $counts elapsed=$($summary.Seconds)s $($summary.Reason)".TrimEnd()
            $line | Add-Content -LiteralPath $record
            Write-Host $line
        }
    }

    # Restore the unmodified model in the workspace, so a later manual build there starts from it.
    [System.IO.File]::WriteAllText((Join-Path $workspaceDirectory $modelPath), $model, [System.Text.UTF8Encoding]::new($false))

    $snapshotAfter = Get-RepositorySnapshot
    $digestsAfter = Get-InputDigests -RelativePaths $inputPaths
    $repositoryUnchanged = Test-SameSnapshot -Before $snapshotBefore -After $snapshotAfter
    $inputsUnchanged = @($inputPaths | Where-Object { $digestsBefore[$_] -cne $digestsAfter[$_] }).Count -eq 0
    "isolation: repository-unchanged=$repositoryUnchanged inputs-unchanged=$inputsUnchanged model-sha256=$($digestsAfter[$modelPath])" |
        Add-Content -LiteralPath $record

    $document = [ordered]@{
        head = $snapshotBefore.Head
        corpusCommit = $corpusCommit
        startedDirty = $snapshotBefore.Status.Length -ne 0
        workspace = $workspaceDirectory
        timeoutFactor = $TimeoutFactor
        minimumTimeoutSeconds = $MinimumTimeoutSeconds
        inputs = $digestsBefore
        fixtureInputs = $fixtureDigests
        repositoryUnchanged = $repositoryUnchanged
        inputsUnchanged = $inputsUnchanged
        baseline = [ordered]@{ seconds = $baselineSeconds; problems = $baselineProblems; run = $baseline }
        mutants = @($results)
    }
    $document | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath (Join-Path $diagnostics "results.json") -Encoding utf8

    $table = @(
        "| Mutant | Group | Verdict | Expect | LanguageSpec | SemanticExplorer | SEM-2C | HostParent | Controls | Elapsed (s) |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    $cell = {
        param($Outcomes, $Corpus)
        $found = @($Outcomes | Where-Object { $_.Corpus -ceq $Corpus })
        if ($found.Count -eq 0) { return "-" }
        $outcome = $found[0]
        switch ($outcome.State) {
            "Clean" { return "0" }
            "GuardsFailed" {
                $note = @()
                if (@($outcome.OtherErrors).Count -gt 0) { $note += "+$(@($outcome.OtherErrors).Count) other" }
                if ($outcome.TimedOut) { $note += "stopped at deadline" }
                if ($outcome.Aborted) { $note += "Lean aborted" }
                if ($note.Count -gt 0) { return "$($outcome.FailingGuards) ($($note -join ', '))" } else { return "$($outcome.FailingGuards)" }
            }
            default { return $outcome.State }
        }
    }
    $table += "| (baseline) | - | $(if ($baselineProblems.Count -eq 0) { 'Clean' } else { 'FAILED' }) | - | " +
        ((@($corpora | ForEach-Object { & $cell $baseline.Corpora $_.Name })) -join " | ") +
        " | $(@($baseline.Controls | ForEach-Object { "$($_.FailingGuards)" }) -join ', ') | $baselineSeconds |"
    foreach ($summary in $results) {
        $controls = if (@($summary.Controls).Count -eq 0) { "-" } else { (@($summary.Controls | ForEach-Object { if ($_.State -ceq "Clean" -or $_.State -ceq "GuardsFailed") { "$($_.FailingGuards)" } else { $_.State } }) -join ", ") }
        $table += "| $($summary.Name) | $($summary.Group) | $($summary.Verdict) | $(if ($summary.Expect) { $summary.Expect } else { '-' }) | " +
            ((@($corpora | ForEach-Object { & $cell $summary.Corpora $_.Name })) -join " | ") + " | $controls | $($summary.Seconds) |"
    }

    $killers = @()
    foreach ($summary in $results) {
        if (@($summary.KillingCases).Count -gt 0) {
            $shown = @($summary.KillingCases | Select-Object -First 12)
            $more = @($summary.KillingCases).Count - $shown.Count
            $killers += "- ``$($summary.Name)``: " + ($shown -join "; ") + $(if ($more -gt 0) { "; and $more more (results.json)" } else { "" })
        }

        foreach ($control in @($summary.Controls)) {
            if (@($control.FailingCases).Count -gt 0) {
                $killers += "- ``$($summary.Name)`` ($($control.Corpus)): " + (@($control.FailingCases) -join "; ")
            }
        }

        if ($summary.Verdict -ceq "Survived") {
            $killers += "- ``$($summary.Name)``: no corpus guard fails" + $(if ($summary.Gap) { " (tracked: $($summary.Gap))" } else { "" })
        }
    }

    $summaryText = @("# Lean-model mutants at $($snapshotBefore.Head)$(if ($corpusCommit) { " (corpora of $corpusCommit)" } else { '' })", "") + $table + @("", "Failing cases and survivors:", "") + $killers +
        @("", "Repository unchanged: $repositoryUnchanged. Inputs unchanged: $inputsUnchanged.")
    $summaryText | Set-Content -LiteralPath (Join-Path $diagnostics "summary.md") -Encoding utf8
    Get-Content -LiteralPath $record | Out-Host
    $problems = @()
    if (-not $repositoryUnchanged) { $problems += "the run changed the repository" }
    if (-not $inputsUnchanged) { $problems += "the run changed a copied input under lean/" }
    foreach ($problem in $baselineProblems) { $problems += "baseline: $problem" }
    foreach ($summary in $results) {
        if (-not $summary.MeetsExpectation) {
            $detail = if (@($summary.MissingRequiredKillers).Count -gt 0 -and $summary.Verdict -ceq "Killed") {
                "killed, but not by $($summary.MissingRequiredKillers -join ', ')"
            }
            elseif ($summary.Expect) { "$($summary.Verdict), expected $($summary.Expect)" }
            else { "$($summary.Verdict): $($summary.Reason)" }
            $problems += "$($summary.Name): $detail $($summary.Reason)".TrimEnd()
        }
    }

    if ($problems.Count -gt 0) {
        throw "the Lean-model mutant campaign did not complete as expected: $($problems -join '; ') (diagnostics: $diagnostics)"
    }
}
finally {
    foreach ($variable in $regenerationFlags) {
        [Environment]::SetEnvironmentVariable($variable.Name, $variable.Value)
    }
    Pop-Location
}
