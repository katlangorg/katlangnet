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

try {
    Push-Location $repoRoot
    $enteredRepo = $true

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
    Write-Host ""
    Write-Host "Validation failed: $($_.Exception.Message)"
    exit 1
}
finally {
    if ($enteredLean) {
        Pop-Location
    }

    if ($enteredRepo) {
        Pop-Location
    }
}
