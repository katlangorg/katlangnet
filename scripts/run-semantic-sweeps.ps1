[CmdletBinding()]
param(
    # The finite semantic-campaign recipes to sweep exhaustively, in order (default: all of them).
    [string[]]$Recipes = @("seed-nested", "seed-nested-wide", "seed-nested-wider"),

    # Members per supervised batch child.
    [ValidateRange(1, 4096)]
    [int]$BatchSize = 128,

    # Each sweep's own time budget; a sweep it stops is incomplete, which fails the script.
    [ValidateRange(60, 21600)]
    [int]$MaxSecondsPerRecipe = 2400
)

# The nightly exhaustive sweeps of the finite semantic-campaign recipes (fuzz/README.md § Campaigns;
# .github/workflows/semantic-nightly.yml). It builds the standalone fuzz consumer once (Debug, so the
# evaluator's DEBUG invariant checks run), then runs `semantic-campaign --exhaustive` for each recipe
# with failures persisted and reduced (batch-only failures as sequences first). Every log, summary and
# reproducer goes to a fresh git-ignored artifacts/validation/semantic-sweeps-* directory (a temporary
# directory if that path is not ignored). It fails when the build fails, when a sweep finds a failure,
# or when a sweep is not complete. It is not a validation level, runs no test, and does not change the
# `validate-all.ps1` phase contract or the build-only standalone-tool job.

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
$project = "fuzz/KatLang.ParserFuzz/KatLang.ParserFuzz.csproj"

function Initialize-Diagnostics {
    # A fresh directory under artifacts/validation/ once git confirms it is ignored, otherwise an
    # external temporary directory. Nothing existing is overwritten or deleted.
    $name = "semantic-sweeps-{0:yyyyMMddTHHmmssZ}-{1}" -f [DateTime]::UtcNow, $PID
    $relative = "artifacts/validation/$name"
    & git check-ignore -q -- "$relative/semantic-sweeps.log"
    $directory = if ($LASTEXITCODE -eq 0) {
        Join-Path $repoRoot $relative
    }
    else {
        Join-Path ([System.IO.Path]::GetTempPath()) "katlang-$name"
    }

    New-Item -ItemType Directory -Force -Path $directory | Out-Null
    return $directory
}

function Write-LogTail {
    param([Parameter(Mandatory = $true)][string]$Path)

    if (Test-Path -LiteralPath $Path) {
        Get-Content -LiteralPath $Path -Tail 40 | Out-Host
    }
}

Push-Location $repoRoot
try {
    # An inherited regeneration flag must never reach a child of this run.
    foreach ($variable in @(Get-ChildItem Env: | Where-Object { $_.Name -like "KATLANG_REGENERATE_*" })) {
        Remove-Item -LiteralPath "Env:$($variable.Name)"
    }

    $diagnostics = Initialize-Diagnostics
    $record = Join-Path $diagnostics "semantic-sweeps.log"
    "semantic sweeps: recipes=$($Recipes -join ',') batch-size=$BatchSize max-seconds-per-recipe=$MaxSecondsPerRecipe" | Set-Content -LiteralPath $record
    Write-Host "Semantic sweep diagnostics: $diagnostics"

    $buildLog = Join-Path $diagnostics "build.log"
    & dotnet build $project -c Debug -p:UseSharedCompilation=false *> $buildLog
    $buildExit = $LASTEXITCODE
    "build: exit=$buildExit" | Add-Content -LiteralPath $record
    if ($buildExit -ne 0) {
        Write-LogTail -Path $buildLog
        throw "the fuzz consumer build failed with exit code $buildExit (log: $buildLog)"
    }

    $assembly = Join-Path $repoRoot "fuzz/KatLang.ParserFuzz/bin/Debug/net11.0/KatLang.ParserFuzz.dll"
    $failed = @()
    $summary = @("| Recipe | Exit | Complete | Planned | Failed | Batch-only | Batch-dependent | Unclassified | Elapsed (s) |", "| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    foreach ($recipe in $Recipes) {
        $out = Join-Path $diagnostics $recipe
        $log = Join-Path $diagnostics "$recipe.log"
        $clock = [System.Diagnostics.Stopwatch]::StartNew()
        & dotnet $assembly semantic-campaign --exhaustive --recipe $recipe --batch-size $BatchSize --max-seconds $MaxSecondsPerRecipe --out $out *> $log
        $exit = $LASTEXITCODE
        $elapsed = [Math]::Round($clock.Elapsed.TotalSeconds)

        $complete = $false
        $planned = "-"
        $failures = "-"
        $batchOnly = "-"
        $batchDependent = "-"
        $unclassified = "-"
        $campaign = Join-Path $out "campaign.json"
        if (Test-Path -LiteralPath $campaign) {
            $json = Get-Content -LiteralPath $campaign -Raw | ConvertFrom-Json
            $complete = [bool]$json.complete
            $planned = $json.planned
            $failures = $json.failed
            $batchOnly = $json.classifications.'batch-only'
            $batchDependent = $json.classifications.'batch-dependent'
            # Batch failures recorded without a standalone rerun once --max-reruns was spent (fuzz/README.md).
            $unclassified = $json.classifications.unclassified
        }

        "${recipe}: exit=$exit complete=$complete planned=$planned failed=$failures batch-only=$batchOnly batch-dependent=$batchDependent unclassified=$unclassified elapsed=${elapsed}s" | Add-Content -LiteralPath $record
        $summary += "| $recipe | $exit | $complete | $planned | $failures | $batchOnly | $batchDependent | $unclassified | $elapsed |"
        Write-LogTail -Path $log
        if ($exit -ne 0 -or -not $complete) {
            $failed += $recipe
        }
    }

    if ($env:GITHUB_STEP_SUMMARY) {
        $summary | Add-Content -LiteralPath $env:GITHUB_STEP_SUMMARY
    }

    Get-Content -LiteralPath $record | Out-Host
    if ($failed.Count -gt 0) {
        throw "semantic sweeps failed or did not complete: $($failed -join ', ') (reproducers: $diagnostics)"
    }
}
finally {
    Pop-Location
}
