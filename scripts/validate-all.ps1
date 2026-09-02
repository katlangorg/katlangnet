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

function Invoke-Native {
    param(
        [Parameter(Mandatory = $true)][string]$FilePath,
        [string[]]$Arguments = @()
    )

    & $FilePath @Arguments
    $exitCode = $LASTEXITCODE
    if ($exitCode -ne 0) {
        throw "Command failed with exit code ${exitCode}: $FilePath $($Arguments -join ' ')"
    }
}

function Invoke-NativeCapture {
    param(
        [Parameter(Mandatory = $true)][string]$FilePath,
        [string[]]$Arguments = @()
    )

    $output = @(& $FilePath @Arguments)
    $exitCode = $LASTEXITCODE
    if ($exitCode -ne 0) {
        throw "Command failed with exit code ${exitCode}: $FilePath $($Arguments -join ' ')"
    }

    return $output
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

        Write-Warning "$Name validation also changed the repository: $($_.Exception.Message)"
    }

    if ($null -ne $phaseFailure) {
        throw $phaseFailure
    }
}

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
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

    Push-Location $repoRoot
    $enteredRepo = $true

    Write-Section "Regeneration flags"
    if ($neutralizedRegenerationFlags.Count -eq 0) {
        Write-Host "No inherited $regenerationFlagPrefix* variables. Verification is observational."
    }
    else {
        Write-Host "Neutralized inherited regeneration flags for this run (restored on exit): $(($neutralizedRegenerationFlags.Name | Sort-Object) -join ', ')"
        Write-Host "Verification never regenerates tracked artifacts; regenerate with a targeted 'dotnet test' run instead."
    }

    if ($Phase -in @("All", "DotNet")) {
        Invoke-ValidationPhase -Name ".NET" -Body {
            # Full-solution build FIRST: dotnet test builds only test projects
            # and their dependency closure, so non-test projects need this
            # independent compile gate.
            Write-Section "Full solution build"
            Invoke-Native -FilePath "dotnet" -Arguments @(
                "build", "./KatLang.slnx", "-p:UseSharedCompilation=false")

            Write-Section "C# test suite"
            Invoke-Native -FilePath "dotnet" -Arguments @(
                "test", "./KatLang.slnx", "-p:UseSharedCompilation=false", "--no-build")

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

    foreach ($entry in $neutralizedRegenerationFlags) {
        try {
            Set-Item -LiteralPath "Env:$($entry.Name)" -Value $entry.Value
        }
        catch {
            $restorationFailures.Add("$($entry.Name): $($_.Exception.Message)")
        }
    }
}

if ($null -ne $validationFailure) {
    Write-Host ""
    Write-Host "Validation failed: $($validationFailure.Exception.Message)"
    if ($restorationFailures.Count -gt 0) {
        Write-Warning "Environment restoration also failed (the validation failure above remains authoritative): $($restorationFailures -join '; ')"
    }
    exit 1
}

if ($restorationFailures.Count -gt 0) {
    throw "Validation passed, but inherited regeneration flags could not be restored: $($restorationFailures -join '; ')"
}
