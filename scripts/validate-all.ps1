[CmdletBinding()]
param(
    [ValidateSet("All", "DotNet", "Lean")]
    [string]$Phase = "All"
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

function Write-Section {
    param([Parameter(Mandatory = $true)][string]$Title)

    Write-Host ""
    Write-Host "==== $Title ===="
}

function Write-ValidationWarning {
    param([Parameter(Mandatory = $true)][string]$Message)

    if ($script:consoleHostLost) {
        # ConsoleHost's warning formatter reads the screen buffer even with redirected streams;
        # that also throws Win32 233 after its console dies. Diagnostics must not interrupt recovery.
        try {
            [Console]::Error.WriteLine("WARNING: $Message")
        }
        catch {
            # Warning output is observational, like the validation record.
        }
    }
    else {
        Write-Warning $Message
    }
}

function Write-ValidationRecord {
    param([AllowEmptyString()][Parameter(Mandatory = $true)][string]$Line)

    # The record is observational: failing to write it never changes the validation result.
    if ($null -eq $script:validationRecordPath) {
        return
    }

    try {
        Add-Content -LiteralPath $script:validationRecordPath -Value $Line -Encoding utf8
    }
    catch {
        Write-ValidationWarning "Could not write the validation record: $($_.Exception.Message)"
    }
}

function Invoke-Native {
    param(
        [Parameter(Mandatory = $true)][string]$FilePath,
        [string[]]$Arguments = @()
    )

    $watch = [System.Diagnostics.Stopwatch]::StartNew()
    $exitCode = $null
    try {
        if ($script:consoleHostLost) {
            $exitCode = Invoke-NativeWithOwnConsole -FilePath $FilePath -Arguments $Arguments
        }
        else {
            # Reset so a lost console can tell a completed command (exit code set) from one that never ran.
            $global:LASTEXITCODE = $null
            try {
                & $FilePath @Arguments
                $exitCode = $LASTEXITCODE
            }
            catch {
                $exitCode = Resolve-ConsoleHostLoss -ErrorRecord $_ -FilePath $FilePath -Arguments $Arguments
            }
        }
    }
    finally {
        $outcome = if ($null -eq $exitCode) { "did not complete" } else { "exit code $exitCode" }
        Write-ValidationRecord "command: $FilePath $($Arguments -join ' ') | $outcome | $([int]$watch.Elapsed.TotalSeconds) s"
    }

    if ($exitCode -ne 0) {
        throw "Command failed with exit code ${exitCode}: $FilePath $($Arguments -join ' ')"
    }
}

# Runs a native command with its standard output (and, with -MergeErrorOutput, its standard error)
# captured as lines. Returns the exit code and the lines; it never throws for a nonzero exit code.
function Invoke-NativeCollect {
    param(
        [Parameter(Mandatory = $true)][string]$FilePath,
        [string[]]$Arguments = @(),
        [switch]$MergeErrorOutput
    )

    # Lines are collected as they arrive, so they survive a host exception raised after the command completed.
    $output = [System.Collections.Generic.List[string]]::new()
    if ($script:consoleHostLost) {
        $exitCode = Invoke-NativeWithOwnConsole -FilePath $FilePath -Arguments $Arguments -Output $output -MergeErrorOutput:$MergeErrorOutput
    }
    else {
        $global:LASTEXITCODE = $null
        try {
            if ($MergeErrorOutput) {
                & $FilePath @Arguments 2>&1 | ForEach-Object { $output.Add("$_") }
            }
            else {
                & $FilePath @Arguments | ForEach-Object { $output.Add($_) }
            }
            $exitCode = $LASTEXITCODE
        }
        catch {
            $exitCode = Resolve-ConsoleHostLoss -ErrorRecord $_ -FilePath $FilePath -Arguments $Arguments -Output $output -MergeErrorOutput:$MergeErrorOutput
        }
    }

    return [pscustomobject]@{ ExitCode = $exitCode; Output = $output.ToArray() }
}

function Invoke-NativeCapture {
    param(
        [Parameter(Mandatory = $true)][string]$FilePath,
        [string[]]$Arguments = @()
    )

    $result = Invoke-NativeCollect -FilePath $FilePath -Arguments $Arguments
    $exitCode = $result.ExitCode
    if ($exitCode -ne 0) {
        throw "Command failed with exit code ${exitCode}: $FilePath $($Arguments -join ' ')"
    }

    return $result.Output
}

# DETACHED CONSOLE (Windows). Around every native command PowerShell's console host saves and then
# restores the console mode and window title (ConsoleHost.NotifyBeginApplication/NotifyEndApplication).
# When the console serving a detached run goes away while this process keeps running (its conhost
# exits, for example with the terminal or agent that started the run), those calls fail with Win32
# error 233 (0xE9, "No process is on the other end of the pipe.") and the host throws a HostException:
# AFTER a command completed ("...while setting the console window title"; $LASTEXITCODE already holds
# that command's real exit code), or BEFORE the next one starts ("...while getting the console mode";
# nothing ran). Console programs started later would inherit the dead console and fail to initialize
# (0xC0000142). So the first such failure switches every later native command to
# Invoke-NativeWithOwnConsole, and the failure itself is resolved exactly: a completed command keeps
# its own exit code (nonzero still fails), a command that never started is started there. Any other
# exception, any other Win32 error, and a lost console without a recorded exit code are rethrown.
$script:consoleHostLost = $false
# Read while the console is alive: PowerShell decodes native output with it, and the fallback decodes
# the same way, so repository fingerprints taken before and after a switch stay comparable.
$script:nativeOutputEncoding = try { [Console]::OutputEncoding } catch { [System.Text.UTF8Encoding]::new($false) }

# Classifies a native-command exception: "after-completion", "before-start", or $null (not a lost console).
function Get-ConsoleHostLoss {
    param([Parameter(Mandatory = $true)][System.Management.Automation.ErrorRecord]$ErrorRecord)

    # Before a command starts the host's failure arrives wrapped in "Program '...' failed to run".
    $wrapped = $false
    $exception = $ErrorRecord.Exception
    while ($null -ne $exception -and $exception -isnot [System.Management.Automation.Host.HostException]) {
        $wrapped = $wrapped -or ($exception -is [System.Management.Automation.ApplicationFailedException])
        $exception = $exception.InnerException
    }

    $errorPipeNotConnected = 233
    if ($null -eq $exception -or $exception.InnerException -isnot [System.ComponentModel.Win32Exception] `
            -or $exception.InnerException.NativeErrorCode -ne $errorPipeNotConnected) {
        return $null
    }

    $errorId = if ($null -ne $exception.ErrorRecord) { $exception.ErrorRecord.FullyQualifiedErrorId } else { "" }
    if (-not $wrapped -and $null -ne $global:LASTEXITCODE -and $errorId -in @("SetConsoleWindowTitle", "SetConsoleMode")) {
        return "after-completion"
    }

    if ($wrapped -and $null -eq $global:LASTEXITCODE -and $errorId -in @("GetConsoleMode", "SetConsoleMode", "RetreiveActiveScreenBufferConsoleHandle")) {
        return "before-start"
    }

    return $null
}

# Called from the catch of a native command run through the console host (with $LASTEXITCODE reset
# before it): returns the command's real exit code when the console went away, else rethrows.
function Resolve-ConsoleHostLoss {
    param(
        [Parameter(Mandatory = $true)][System.Management.Automation.ErrorRecord]$ErrorRecord,
        [Parameter(Mandatory = $true)][string]$FilePath,
        [string[]]$Arguments = @(),
        [System.Collections.Generic.List[string]]$Output,
        [switch]$MergeErrorOutput
    )

    $loss = Get-ConsoleHostLoss -ErrorRecord $ErrorRecord
    if ($null -eq $loss) {
        throw $ErrorRecord
    }

    $command = "$FilePath $($Arguments -join ' ')"
    $message = ($ErrorRecord.Exception.Message -split "`r?`n")[0]
    Write-ValidationRecord "console host lost ($loss): $command | $message"
    if (-not $script:consoleHostLost) {
        $script:consoleHostLost = $true
        Write-ValidationWarning "The console of this run went away ($loss of '$command'): $message Later native commands run in a hidden console of their own."
    }

    if ($loss -eq "after-completion") {
        return $global:LASTEXITCODE
    }

    if ($null -ne $Output) {
        $Output.Clear()
    }
    return Invoke-NativeWithOwnConsole -FilePath $FilePath -Arguments $Arguments -Output $Output -MergeErrorOutput:$MergeErrorOutput
}

# Starts a native command directly, in a hidden console of its own, with the same arguments, working
# directory, environment and output decoding as `& $FilePath @Arguments`. Standard output goes to
# $Output when given, otherwise line by line to the host; standard error is added to $Output with
# -MergeErrorOutput, otherwise written to this process's standard error. Returns the exit code.
function Invoke-NativeWithOwnConsole {
    param(
        [Parameter(Mandatory = $true)][string]$FilePath,
        [string[]]$Arguments = @(),
        [System.Collections.Generic.List[string]]$Output,
        [switch]$MergeErrorOutput
    )

    $startInfo = [System.Diagnostics.ProcessStartInfo]::new($FilePath)
    foreach ($argument in $Arguments) {
        $startInfo.ArgumentList.Add($argument)
    }
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.WorkingDirectory = (Get-Location).ProviderPath
    $startInfo.RedirectStandardInput = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    $startInfo.StandardOutputEncoding = $script:nativeOutputEncoding
    $startInfo.StandardErrorEncoding = $script:nativeOutputEncoding

    $process = [System.Diagnostics.Process]::Start($startInfo)
    try {
        $process.StandardInput.Close()
        $errorText = $process.StandardError.ReadToEndAsync()
        while ($null -ne ($line = $process.StandardOutput.ReadLine())) {
            if ($null -ne $Output) {
                $Output.Add($line)
            }
            else {
                Write-Host $line
            }
        }
        $process.WaitForExit()

        $errors = $errorText.GetAwaiter().GetResult()
        if ($errors.Length -gt 0) {
            if ($MergeErrorOutput -and $null -ne $Output) {
                foreach ($line in ($errors.TrimEnd("`r", "`n") -split "`r?`n")) {
                    $Output.Add($line)
                }
            }
            else {
                [Console]::Error.Write($errors)
            }
        }

        return $process.ExitCode
    }
    finally {
        $process.Dispose()
    }
}

function Get-TextDigest {
    param([AllowEmptyString()][Parameter(Mandatory = $true)][string]$Text)

    $bytes = [System.Text.Encoding]::UTF8.GetBytes($Text)
    return [System.Convert]::ToHexString([System.Security.Cryptography.SHA256]::HashData($bytes))
}

function Get-RepositorySnapshot {
    # Keep the index and worktree fingerprints separate. A simple porcelain
    # snapshot would miss a test rewriting a file that was already modified
    # when local validation began because its status code could remain "M".
    $status = (Invoke-NativeCapture -FilePath "git" -Arguments @(
        "status", "--porcelain=v1", "--untracked-files=all")) -join "`n"
    $indexDiff = (Invoke-NativeCapture -FilePath "git" -Arguments @(
        "diff", "--cached", "--binary", "--no-ext-diff", "--no-textconv", "--")) -join "`n"
    $worktreeDiff = (Invoke-NativeCapture -FilePath "git" -Arguments @(
        "diff", "--binary", "--no-ext-diff", "--no-textconv", "--")) -join "`n"

    $untrackedRows = [System.Collections.Generic.List[string]]::new()
    $untrackedPaths = @(Invoke-NativeCapture -FilePath "git" -Arguments @(
        "ls-files", "--others", "--exclude-standard")) | Sort-Object
    foreach ($path in $untrackedPaths) {
        $objectId = (Invoke-NativeCapture -FilePath "git" -Arguments @(
            "hash-object", "--no-filters", "--", $path)) -join ""
        $untrackedRows.Add("$path`0$objectId")
    }

    return [pscustomobject]@{
        Status = $status
        IndexDigest = Get-TextDigest -Text $indexDiff
        WorktreeDigest = Get-TextDigest -Text $worktreeDiff
        UntrackedDigest = Get-TextDigest -Text ($untrackedRows -join "`n")
    }
}

function Assert-RepositoryUnchanged {
    param(
        [Parameter(Mandatory = $true)]$Before,
        [Parameter(Mandatory = $true)][string]$PhaseName
    )

    $after = Get-RepositorySnapshot
    $same = $Before.Status -ceq $after.Status `
        -and $Before.IndexDigest -ceq $after.IndexDigest `
        -and $Before.WorktreeDigest -ceq $after.WorktreeDigest `
        -and $Before.UntrackedDigest -ceq $after.UntrackedDigest

    if (-not $same) {
        throw "$PhaseName validation changed the repository. Validation must preserve pre-existing staged, unstaged, and untracked content exactly."
    }

    # In CI (and any other initially clean checkout), also run the familiar
    # direct checks so their diagnostics identify an unexpected tracked or
    # untracked path immediately. Dirty developer checkouts use the stronger
    # before/after comparison above and are not rejected merely for starting
    # dirty.
    if ($Before.Status.Length -eq 0) {
        Invoke-Native -FilePath "git" -Arguments @("diff", "--exit-code", "--")
        $unexpectedStatus = (Invoke-NativeCapture -FilePath "git" -Arguments @(
            "status", "--porcelain=v1", "--untracked-files=all")) -join "`n"
        if ($unexpectedStatus.Length -ne 0) {
            throw "$PhaseName validation left unexpected repository status:`n$unexpectedStatus"
        }
    }

    Write-Host "$PhaseName validation left the repository unchanged."
}

function Initialize-ValidationDiagnostics {
    # Diagnostics go only where they cannot change the fingerprinted repository state: a fresh
    # directory under artifacts/validation/ once git confirms it is ignored, otherwise an external
    # temporary directory. Nothing existing is overwritten or deleted.
    $name = "validate-all-{0}-{1:yyyyMMddTHHmmssZ}-{2}" -f $Phase.ToLowerInvariant(), [DateTime]::UtcNow, $PID
    $relative = "artifacts/validation/$name"
    # The run's first native command, so the console host cannot have been lost before it.
    $global:LASTEXITCODE = $null
    try {
        & git check-ignore -q -- "$relative/validation-record.txt"
        $ignoreExitCode = $LASTEXITCODE
    }
    catch {
        $ignoreExitCode = Resolve-ConsoleHostLoss -ErrorRecord $_ -FilePath "git" -Arguments @(
            "check-ignore", "-q", "--", "$relative/validation-record.txt")
    }
    $directory = if ($ignoreExitCode -eq 0) {
        Join-Path $repoRoot $relative
    }
    else {
        Join-Path ([System.IO.Path]::GetTempPath()) "katlang-$name"
    }

    New-Item -ItemType Directory -Force -Path $directory | Out-Null
    return $directory
}

function Write-ValidationEnvironment {
    try {
        $runtime = [System.Runtime.InteropServices.RuntimeInformation]
        Write-ValidationRecord "validate-all.ps1 -Phase $Phase"
        Write-ValidationRecord "started (UTC): $([DateTime]::UtcNow.ToString('o'))"
        Write-ValidationRecord "host: $($runtime::OSDescription); $($runtime::OSArchitecture); PowerShell $($PSVersionTable.PSVersion); $([Environment]::ProcessorCount) processors"
        foreach ($name in @("GITHUB_WORKFLOW", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_SHA", "GITHUB_REF", "RUNNER_OS", "RUNNER_ARCH", "ImageOS", "ImageVersion")) {
            $value = [Environment]::GetEnvironmentVariable($name)
            if (-not [string]::IsNullOrEmpty($value)) {
                Write-ValidationRecord "${name}: $value"
            }
        }

        $head = (Invoke-NativeCapture -FilePath "git" -Arguments @("rev-parse", "HEAD")) -join ""
        $status = @(Invoke-NativeCapture -FilePath "git" -Arguments @("status", "--porcelain=v1", "--untracked-files=all"))
        $state = if ($status.Count -eq 0) { "clean" } else { "$($status.Count) changed or untracked path(s)" }
        Write-ValidationRecord "git HEAD: $head; initial status: $state"
        foreach ($line in ($status | Select-Object -First 50)) {
            Write-ValidationRecord "  $line"
        }

        if ($neutralizedRegenerationFlags.Count -gt 0) {
            Write-ValidationRecord "neutralized: $(($neutralizedRegenerationFlags.Name | Sort-Object) -join ', ')"
        }

        foreach ($entry in @(Get-ChildItem -Path Env: | Where-Object { $_.Name -match '^(DOTNET_|COMPlus_|KATLANG_)' } | Sort-Object Name)) {
            Write-ValidationRecord "env $($entry.Name)=$($entry.Value)"
        }

        if ($Phase -in @("All", "DotNet")) {
            Write-ValidationRecord "dotnet SDK: $((Invoke-NativeCollect -FilePath "dotnet" -Arguments @("--version") -MergeErrorOutput).Output -join ' ')"
            foreach ($line in @((Invoke-NativeCollect -FilePath "dotnet" -Arguments @("--list-runtimes") -MergeErrorOutput).Output)) {
                Write-ValidationRecord "  $line"
            }
        }
    }
    catch {
        Write-ValidationWarning "Could not record the validation environment: $($_.Exception.Message)"
    }
}

function Write-TestResultSummary {
    param(
        [Parameter(Mandatory = $true)][string]$Directory,
        [Parameter(Mandatory = $true)][int]$ExpectedFiles
    )

    # Observational: a summary problem is reported as a warning and never alters the test result.
    try {
        $files = @(if (Test-Path -LiteralPath $Directory) {
                Get-ChildItem -LiteralPath $Directory -Filter "*.trx" -File | Sort-Object Name
            })
        $lines = [System.Collections.Generic.List[string]]::new()
        $lines.Add("$($files.Count) TRX file(s) in ${Directory}:")
        if ($files.Count -ne $ExpectedFiles) {
            $lines.Add("WARNING: expected one TRX file per test project ($ExpectedFiles); a missing file means that project's run did not complete.")
        }

        foreach ($file in $files) {
            $trx = [xml](Get-Content -LiteralPath $file.FullName -Raw)
            $ns = [System.Xml.XmlNamespaceManager]::new($trx.NameTable)
            $ns.AddNamespace("t", "http://microsoft.com/schemas/VisualStudio/TeamTest/2010")
            $summary = $trx.SelectSingleNode("/t:TestRun/t:ResultSummary", $ns)
            $counters = $trx.SelectSingleNode("/t:TestRun/t:ResultSummary/t:Counters", $ns)
            $method = $trx.SelectSingleNode("/t:TestRun/t:TestDefinitions/t:UnitTest/t:TestMethod", $ns)
            $assembly = if ($null -ne $method) { [System.IO.Path]::GetFileName($method.GetAttribute("codeBase")) } else { "(no tests)" }
            $outcome = if ($null -ne $summary) { $summary.GetAttribute("outcome") } else { "(no summary)" }
            $counts = if ($null -ne $counters) {
                "total $($counters.GetAttribute('total')), executed $($counters.GetAttribute('executed')), passed $($counters.GetAttribute('passed')), failed $($counters.GetAttribute('failed'))"
            }
            else {
                "no counters"
            }
            $lines.Add("- ${assembly}: $outcome; $counts ($($file.Name))")

            $failed = @($trx.SelectNodes("/t:TestRun/t:Results/t:UnitTestResult[@outcome='Failed']", $ns))
            foreach ($result in ($failed | Select-Object -First 20)) {
                $message = $result.SelectSingleNode("t:Output/t:ErrorInfo/t:Message", $ns)
                $detail = if ($null -ne $message) {
                    @($message.InnerText -split "?
" | Where-Object { $_.Trim().Length -gt 0 } | Select-Object -First 3) -join " / "
                }
                else {
                    "(no message)"
                }
                $lines.Add("  FAILED $($result.GetAttribute('testName')): $detail")
            }
            if ($failed.Count -gt 20) {
                $lines.Add("  ... and $($failed.Count - 20) more failed test(s); see $($file.Name)")
            }
        }

        $text = $lines -join "`n"
        Write-Host $text
        Set-Content -LiteralPath (Join-Path $diagnosticsDirectory "test-summary.txt") -Value $text -Encoding utf8
        if (-not [string]::IsNullOrEmpty($env:GITHUB_STEP_SUMMARY)) {
            $fence = '```'
            Add-Content -LiteralPath $env:GITHUB_STEP_SUMMARY -Encoding utf8 -Value "### .NET test results`n`n${fence}text`n$text`n$fence`n"
        }
    }
    catch {
        Write-ValidationWarning "Could not summarize the test results: $($_.Exception.Message)"
    }
}

function Invoke-ValidationPhase {
    param(
        [Parameter(Mandatory = $true)][string]$Name,
        [Parameter(Mandatory = $true)][scriptblock]$Body
    )

    $before = Get-RepositorySnapshot
    $phaseFailure = $null
    try {
        & $Body
    }
    catch {
        $phaseFailure = $_
    }

    try {
        Assert-RepositoryUnchanged -Before $before -PhaseName $Name
    }
    catch {
        if ($null -eq $phaseFailure) {
            throw
        }

        Write-ValidationWarning "$Name validation also changed the repository: $($_.Exception.Message)"
    }

    if ($null -ne $phaseFailure) {
        throw $phaseFailure
    }
}

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
$script:validationRecordPath = $null
$diagnosticsDirectory = $null
$testDiagnosticsVariable = "KATLANG_TEST_DIAGNOSTICS_DIR"
$enteredRepo = $false
$enteredLean = $false
$validationFailure = $null
$restorationFailures = [System.Collections.Generic.List[string]]::new()
$leanTargets = @(
    "CoreTests",
    "KatLangArityLaws",
    "AstDemo",
    "CoreArityAlgebra",
    "CoreArityAlgebraProofs",
    "SemanticExplorerCases",
    "LanguageSpecCases"
)

# Verification is OBSERVATIONAL. A KATLANG_REGENERATE_* flag inherited from the
# calling shell would otherwise turn artifact tests into regeneration runs.
# Remove the whole case-insensitive namespace from this process and restore it
# exactly on exit; regeneration remains a separate targeted test invocation.
$regenerationFlagPrefix = "KATLANG_REGENERATE_"
$neutralizedRegenerationFlags = [System.Collections.Generic.List[object]]::new()

# The invocation-plan mode is process-wide test-host configuration read once at test-assembly load
# (ForcedInvocationPlansHook), so it is fixed here, before any test host starts, and inherited by
# every test host and child host. Always REMOVE the inherited diagnostic flag: normal validation
# runs the suite once on the production gate, with route comparisons inside dedicated tests.
# Restore the caller's environment exactly on exit.
$planModeVariable = "KATLANG_FORCE_INVOCATION_PLANS"
$inheritedPlanMode = [Environment]::GetEnvironmentVariable($planModeVariable)

function Set-PlanModeVariable {
    param([AllowNull()][object]$Value)

    # Through the Env: drive, never [Environment]::SetEnvironmentVariable: PowerShell passes $null
    # to a .NET string parameter as "", which leaves an EMPTY variable instead of removing it.
    if ($null -eq $Value) {
        if (Test-Path -LiteralPath "Env:$planModeVariable") {
            Remove-Item -LiteralPath "Env:$planModeVariable"
        }
    }
    else {
        Set-Item -LiteralPath "Env:$planModeVariable" -Value $Value
    }
}

try {
    # Keep one entry per environment entry rather than a PowerShell hashtable:
    # case-sensitive hosts can contain names that differ only by case, whereas
    # PowerShell hashtable keys are case-insensitive.
    foreach ($entry in @(Get-ChildItem -Path Env:)) {
        if ($entry.Name.StartsWith($regenerationFlagPrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
            $neutralizedRegenerationFlags.Add([pscustomobject]@{ Name = $entry.Name; Value = $entry.Value })
            Remove-Item -LiteralPath "Env:$($entry.Name)"
        }
    }

    Set-PlanModeVariable -Value $null

    Push-Location $repoRoot
    $enteredRepo = $true

    Write-Section "Validation diagnostics"
    $diagnosticsDirectory = Initialize-ValidationDiagnostics
    $script:validationRecordPath = Join-Path $diagnosticsDirectory "validation-record.txt"
    Write-ValidationEnvironment
    Write-Host "Command record, test results and allocation-probe logs: $diagnosticsDirectory"

    Write-Section "Regeneration flags"
    if ($neutralizedRegenerationFlags.Count -eq 0) {
        Write-Host "No inherited $regenerationFlagPrefix* variables. Verification is observational."
    }
    else {
        Write-Host "Neutralized inherited regeneration flags for this run (restored on exit): $(($neutralizedRegenerationFlags.Name | Sort-Object) -join ', ')"
        Write-Host "Verification never regenerates tracked artifacts; regenerate with a targeted 'dotnet test' run instead."
    }

    Write-Section "Invocation-plan mode"
    Write-Host "Ordinary: $planModeVariable is unset for every test host$(if ($null -ne $inheritedPlanMode) { ' (inherited value removed, restored on exit)' })."
    Write-ValidationRecord "invocation-plan mode: ordinary"

    if ($Phase -in @("All", "DotNet")) {
        Invoke-ValidationPhase -Name ".NET" -Body {
            # Full-solution build FIRST: dotnet test builds only test projects
            # and their dependency closure, so non-test projects need this
            # independent compile gate.
            Write-Section "Full solution build"
            Invoke-Native -FilePath "dotnet" -Arguments @(
                "build", "./KatLang.slnx", "-p:UseSharedCompilation=false")

            Write-Section "C# test suite"
            # One TRX per test project: the logger reserves each prefix_framework_timestamp file
            # with CreateNew and moves to the next free name, so projects never overwrite each other.
            $testResults = Join-Path $diagnosticsDirectory "test-results"
            $testProjects = (Select-String -LiteralPath "./KatLang.slnx" -Pattern 'Path="tests/' -AllMatches).Matches.Count
            $inheritedTestDiagnostics = [Environment]::GetEnvironmentVariable($testDiagnosticsVariable)
            [Environment]::SetEnvironmentVariable($testDiagnosticsVariable, $diagnosticsDirectory)
            try {
                Invoke-Native -FilePath "dotnet" -Arguments @(
                    "test", "./KatLang.slnx", "-p:UseSharedCompilation=false", "--no-build",
                    "--logger", "trx;LogFilePrefix=katlang", "--results-directory", $testResults)
            }
            finally {
                [Environment]::SetEnvironmentVariable($testDiagnosticsVariable, $inheritedTestDiagnostics)
                Write-TestResultSummary -Directory $testResults -ExpectedFiles $testProjects
            }

            Write-Section "Git diff check"
            Invoke-Native -FilePath "git" -Arguments @("diff", "--check")
        }
    }

    if ($Phase -in @("All", "Lean")) {
        Invoke-ValidationPhase -Name "Lean" -Body {
            Push-Location "./lean"
            $enteredLean = $true
            try {
                foreach ($target in $leanTargets) {
                    Write-Section "Lean $target"
                    Invoke-Native -FilePath "lake" -Arguments @("build", $target)
                }
            }
            finally {
                Pop-Location
                $enteredLean = $false
            }
        }
    }

    Write-Section "Validation complete ($Phase)"
}
catch {
    # Defer reporting/exiting until after finally so environment restoration
    # runs even when a native validation command fails.
    $validationFailure = $_
}
finally {
    if ($enteredLean) {
        Pop-Location
    }

    if ($enteredRepo) {
        Pop-Location
    }

    try {
        Set-PlanModeVariable -Value $inheritedPlanMode
    }
    catch {
        $restorationFailures.Add("${planModeVariable}: $($_.Exception.Message)")
    }

    foreach ($entry in $neutralizedRegenerationFlags) {
        try {
            Set-Item -LiteralPath "Env:$($entry.Name)" -Value $entry.Value
        }
        catch {
            $restorationFailures.Add("$($entry.Name): $($_.Exception.Message)")
        }
    }
}

$result = if ($null -ne $validationFailure) { "FAILED: $($validationFailure.Exception.Message)" } else { "passed" }
Write-ValidationRecord "finished (UTC): $([DateTime]::UtcNow.ToString('o')); result: $result"
if ($null -ne $diagnosticsDirectory) {
    Write-Host "Validation diagnostics: $diagnosticsDirectory"
}

if ($null -ne $validationFailure) {
    Write-Host ""
    Write-Host "Validation failed: $($validationFailure.Exception.Message)"
    if ($restorationFailures.Count -gt 0) {
        Write-ValidationWarning "Environment restoration also failed (the validation failure above remains authoritative): $($restorationFailures -join '; ')"
    }
    exit 1
}

if ($restorationFailures.Count -gt 0) {
    throw "Validation passed, but inherited environment variables could not be restored: $($restorationFailures -join '; ')"
}
