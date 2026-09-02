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

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
$enteredRepo = $false
$enteredLean = $false
$validationFailure = $null
$restorationFailures = [System.Collections.Generic.List[string]]::new()

# Verification is OBSERVATIONAL. A KATLANG_REGENERATE_* flag inherited from the
# calling shell would otherwise turn the artifact tests into regeneration runs
# that rewrite tracked generated files (the Lean corpora, the generator prompt
# blocks, the public API baseline), so every variable in that namespace is
# removed from this process - and therefore from every dotnet/lake child -
# before anything that could observe it runs. The whole PREFIX is cleared,
# case-insensitively (Windows environment names are case-insensitive), rather
# than a hand-maintained list, so a future flag cannot escape by being
# forgotten here; the registry of flags and the write-then-fail regeneration
# contract live in tests/KatLang.Tests/Infrastructure/ArtifactRegeneration.cs.
# The removal is process-local and the original values are restored on exit,
# so an interactive caller's session is left exactly as it was found.
# Regeneration is always a separate, deliberate, targeted `dotnet test` run
# that writes the artifact and then fails by design.
$regenerationFlagPrefix = "KATLANG_REGENERATE_"
$neutralizedRegenerationFlags = [System.Collections.Generic.List[object]]::new()

try {
    # Keep one entry per environment entry rather than a PowerShell hashtable:
    # on case-sensitive platforms two variables can differ only by case, while
    # PowerShell hashtable keys are case-insensitive. A list restores both
    # entries exactly. Capture/removal is inside the try so even a partial
    # neutralization is unwound by finally.
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

    # Full-solution build FIRST: `dotnet test` only builds test projects and
    # their dependency closure, so a compile break in a non-test project
    # (benchmarks, DemoApp) would otherwise pass validation undetected — as
    # happened during the Track A gate review.
    Write-Section "Full solution build"
    Invoke-Native -FilePath "dotnet" -Arguments @("build", ".\KatLang.slnx", "-p:UseSharedCompilation=false")

    Write-Section "C# test suite"
    Invoke-Native -FilePath "dotnet" -Arguments @("test", ".\KatLang.slnx", "-p:UseSharedCompilation=false", "--no-build")

    Write-Section "Git diff check"
    Invoke-Native -FilePath "git" -Arguments @("diff", "--check")

    Write-Section "Lean CoreTests"
    Push-Location ".\lean"
    $enteredLean = $true
    Invoke-Native -FilePath "lake" -Arguments @("build", "CoreTests")

    Write-Section "Lean KatLangArityLaws"
    Invoke-Native -FilePath "lake" -Arguments @("build", "KatLangArityLaws")

    Write-Section "Lean AstDemo"
    Invoke-Native -FilePath "lake" -Arguments @("build", "AstDemo")

    Write-Section "Lean CoreArityAlgebra"
    Invoke-Native -FilePath "lake" -Arguments @("build", "CoreArityAlgebra")

    Write-Section "Lean CoreArityAlgebraProofs"
    Invoke-Native -FilePath "lake" -Arguments @("build", "CoreArityAlgebraProofs")

    Write-Section "Lean SemanticExplorerCases (Lean/C# differential corpus)"
    Invoke-Native -FilePath "lake" -Arguments @("build", "SemanticExplorerCases")

    Write-Section "Lean LanguageSpecCases (canonical executable language specification)"
    Invoke-Native -FilePath "lake" -Arguments @("build", "LanguageSpecCases")

    Pop-Location
    $enteredLean = $false

    Write-Section "Validation complete"
}
catch {
    # Defer reporting/exiting until after finally. That keeps the original
    # validation failure authoritative even if restoring an environment entry
    # also encounters a host-level problem.
    $validationFailure = $_
}
finally {
    if ($enteredLean) {
        Pop-Location
    }

    if ($enteredRepo) {
        Pop-Location
    }

    # Leave the caller's process environment as it was found.
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
