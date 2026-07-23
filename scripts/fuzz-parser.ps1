<#
.SYNOPSIS
    Runs a bounded coverage-guided fuzzing campaign against the raw KatLang parser
    (Parser.ParseSyntax) using SharpFuzz + libFuzzer.

.DESCRIPTION
    This machine has the .NET 10 SDK on Windows but no native clang/libFuzzer, so the
    actual libFuzzer run is delegated to WSL (which has clang and can build the
    libfuzzer-dotnet fork-server driver). The harness is cross-published self-contained
    for linux-x64, so WSL needs no .NET install of its own.

    Pipeline:
      1. dotnet publish the harness self-contained for linux-x64 (fuzz/artifacts/publish-linux).
      2. Instrument KatLang.dll (the target) with the `sharpfuzz` global tool.
      3. In WSL: build/cache the libfuzzer-dotnet driver, then run libFuzzer with the
         seed corpus + dictionary and the campaign bounds (fuzz/run-campaign.sh).

    Seeds (fuzz/KatLang.ParserFuzz/Testcases) are read-only during the run. New
    coverage-increasing inputs and crash artifacts are written under fuzz/artifacts/
    (gitignored). This project is NOT part of KatLang.slnx, so normal validation is
    unaffected.

.NOTES
    Requires: .NET 10 SDK (Windows); a WSL distro with clang (e.g. Ubuntu); internet
    access on first run (to fetch the driver source and, if missing, the sharpfuzz tool).
    Written for Windows PowerShell 5.1.

.EXAMPLE
    powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1
    # default: 600s campaign, 16 KiB max input, 5s per-input timeout, 2 GiB RSS limit

.EXAMPLE
    powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 -MaxTotalTime 60 -FreshCorpus

.EXAMPLE
    powershell -ExecutionPolicy Bypass -File scripts\fuzz-parser.ps1 -Mode metamorphic -MaxTotalTime 300 -MaxLen 4096
    # operational-metamorphic target; seeds are exported from the curated manifest and the
    # corpus/crash directories are kept separate from the raw-parser campaign's.
#>
[CmdletBinding()]
param(
    [int]$MaxTotalTime = 600,    # total campaign wall-clock seconds
    [int]$MaxLen = 16384,        # max input length in bytes (16 KiB)
    [int]$Timeout = 5,           # per-input timeout in seconds
    [int]$RssLimitMb = 2048,     # memory limit (~2 GiB)
    [string]$Distro = '',        # optional specific WSL distro (else the WSL default)
    [string]$Mode = '',          # KATLANG_FUZZ_MODE: '' = raw parser, frontend, evaluator, metamorphic, utf16
    [string]$SeedDir = '',       # override the read-only seed corpus (else the mode's default)
    [int]$FuzzerSeed = 0,        # fixed libFuzzer -seed (0 = engine picks its own, as before)
    [switch]$FreshCorpus,        # clear the writable corpus before running
    [switch]$SkipBuild           # reuse an existing publish + instrumentation
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

function Write-Section([string]$Title) {
    Write-Host ''
    Write-Host "==== $Title ===="
}

$repoRoot   = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$fuzzDir    = Join-Path $repoRoot 'fuzz'
$proj       = Join-Path $fuzzDir 'KatLang.ParserFuzz\KatLang.ParserFuzz.csproj'
$publishDir = Join-Path $fuzzDir 'artifacts\publish-linux'
$dictFile   = Join-Path $fuzzDir 'katlang.dict'
$runnerSh   = Join-Path $fuzzDir 'run-campaign.sh'
$targetDll  = Join-Path $publishDir 'KatLang.dll'

# Each target keeps its own writable corpus and crash directory, so switching modes never
# mixes one target's coverage-increasing inputs into another's. An unset -Mode is the raw
# parser and keeps the original paths, leaving existing campaigns byte-for-byte unchanged.
$suffix = ''
if ($Mode -ne '') { $suffix = "-$Mode" }
$corpusDir  = Join-Path $fuzzDir "artifacts\corpus$suffix"
$crashDir   = Join-Path $fuzzDir "artifacts\crashes$suffix"

if ($SeedDir -ne '') {
    $seedDir = $SeedDir
}
elseif ($Mode -eq 'metamorphic') {
    # Metamorphic seeds are template payloads, not source files, so the read-only seed corpus
    # is materialized from the tracked manifest — one source of truth for fuzzing and replay.
    #
    # The export directory is entirely script-owned and the export is deterministic from the
    # manifest, so it is CLEARED first. Without that, seeds a manifest no longer contains survive
    # as files and quietly join every later campaign: the run still only sees valid payloads, but
    # it is no longer seeded from the tracked corpus, and two people running the same command from
    # the same commit start from different seed sets. The export tool reports the leftovers rather
    # than deleting them, because the directory belongs to its caller — which is here.
    $seedDir  = Join-Path $fuzzDir 'artifacts\metamorphic-seeds'
    $manifest = Join-Path $fuzzDir 'KatLang.ParserFuzz\MetamorphicTestcases'
    Write-Section 'Export curated metamorphic seeds'
    if (Test-Path $seedDir) { Remove-Item -Recurse -Force $seedDir }
    & dotnet run --project $proj -- metamorphic-seeds $seedDir $manifest
    if ($LASTEXITCODE -ne 0) { throw 'metamorphic-seeds export failed.' }
}
elseif ($Mode -eq 'utf16') {
    # UTF-16 seeds are template payloads for the same reason metamorphic ones are, plus a stronger
    # one: a seed containing an isolated surrogate has NO UTF-8 form, so storing it as source text
    # would let git or an editor rewrite it to U+FFFD and the seed would silently stop testing the
    # thing it names. Same script-owned, cleared-then-regenerated export directory.
    $seedDir  = Join-Path $fuzzDir 'artifacts\utf16-seeds'
    $manifest = Join-Path $fuzzDir 'KatLang.ParserFuzz\Utf16Testcases'
    Write-Section 'Export curated UTF-16 seeds'
    if (Test-Path $seedDir) { Remove-Item -Recurse -Force $seedDir }
    & dotnet run --project $proj -- utf16-seeds $seedDir $manifest
    if ($LASTEXITCODE -ne 0) { throw 'utf16-seeds export failed.' }
}
elseif ($Mode -eq 'editor') {
    # Editor seeds are template payloads for the same reasons the UTF-16 ones are: they select a
    # template plus difficult UTF-16 code units, and an isolated surrogate has no UTF-8 form, so
    # storing built source would rewrite it. Same script-owned, cleared-then-regenerated directory.
    $seedDir  = Join-Path $fuzzDir 'artifacts\editor-seeds'
    $manifest = Join-Path $fuzzDir 'KatLang.ParserFuzz\EditorTestcases'
    Write-Section 'Export curated editor seeds'
    if (Test-Path $seedDir) { Remove-Item -Recurse -Force $seedDir }
    & dotnet run --project $proj -- editor-seeds $seedDir $manifest
    if ($LASTEXITCODE -ne 0) { throw 'editor-seeds export failed.' }
}
else {
    $seedDir = Join-Path $fuzzDir 'KatLang.ParserFuzz\Testcases'
}

# The harness reads KATLANG_FUZZ_MODE inside WSL, so forward it explicitly through WSLENV.
function Add-WslEnv([string]$Name) {
    $existingWslEnv = [Environment]::GetEnvironmentVariable('WSLENV')
    if ([string]::IsNullOrEmpty($existingWslEnv)) { $env:WSLENV = $Name }
    elseif (($existingWslEnv -split ':') -notcontains $Name) { $env:WSLENV = "${existingWslEnv}:$Name" }
}

if ($Mode -ne '') {
    $env:KATLANG_FUZZ_MODE = $Mode
    Add-WslEnv 'KATLANG_FUZZ_MODE'
}

# A fixed engine seed makes one campaign reproducible and makes two campaigns genuinely
# INDEPENDENT rather than two samples of the same stream — which is the whole point of running a
# confirmation campaign after a main one. Zero (the default) leaves libFuzzer to pick its own,
# exactly as before.
if ($FuzzerSeed -ne 0) {
    $env:KATLANG_FUZZ_SEED = $FuzzerSeed
    Add-WslEnv 'KATLANG_FUZZ_SEED'
}

# WSL invocation prefix (optionally pin a distro).
$wslPrefix = @()
if ($Distro -ne '') { $wslPrefix = @('-d', $Distro) }

function Test-Wsl {
    & wsl @wslPrefix -e true 2>$null
    if ($LASTEXITCODE -ne 0) { throw "WSL is not usable (wsl -e true failed). Install/enable a WSL distro with clang." }
}

function ConvertTo-WslPath([string]$Path) {
    $out = & wsl @wslPrefix -e wslpath -a -u "$Path"
    if ($LASTEXITCODE -ne 0) { throw "wslpath failed for '$Path'." }
    return ([string]($out | Select-Object -First 1)).Trim()
}

Test-Wsl

if (-not $SkipBuild) {
    Write-Section 'Publish (self-contained linux-x64)'
    if (Test-Path $publishDir) { Remove-Item -Recurse -Force $publishDir }
    & dotnet publish $proj -c Release -r linux-x64 --self-contained true -o $publishDir
    if ($LASTEXITCODE -ne 0) { throw 'dotnet publish failed.' }

    Write-Section 'Instrument KatLang.dll (sharpfuzz)'
    $sharpfuzz = Get-Command sharpfuzz -ErrorAction SilentlyContinue
    if (-not $sharpfuzz) {
        Write-Host 'sharpfuzz tool not found; installing SharpFuzz.CommandLine globally...'
        & dotnet tool install --global SharpFuzz.CommandLine
        $toolsDir = Join-Path $env:USERPROFILE '.dotnet\tools'
        if (Test-Path $toolsDir) { $env:PATH = "$toolsDir;$env:PATH" }
        $sharpfuzz = Get-Command sharpfuzz -ErrorAction SilentlyContinue
        if (-not $sharpfuzz) { throw "sharpfuzz not found after install; ensure $toolsDir is on PATH." }
    }
    & sharpfuzz $targetDll
    if ($LASTEXITCODE -ne 0) { throw "sharpfuzz instrumentation failed (exit $LASTEXITCODE)." }
}
else {
    if (-not (Test-Path $targetDll)) { throw "-SkipBuild set but no publish found at $publishDir. Run without -SkipBuild first." }
}

Write-Section 'Prepare corpus / crash directories'
if ($FreshCorpus -and (Test-Path $corpusDir)) { Remove-Item -Recurse -Force $corpusDir }
New-Item -ItemType Directory -Force -Path $corpusDir | Out-Null
New-Item -ItemType Directory -Force -Path $crashDir  | Out-Null
Write-Host "corpus (writable): $corpusDir"
Write-Host "seeds  (readonly): $seedDir"
Write-Host "crashes:           $crashDir"

$modeLabel = 'raw parser (default)'
if ($Mode -ne '') { $modeLabel = $Mode }
Write-Section "Run libFuzzer in WSL ($MaxTotalTime s) - target: $modeLabel"
$args = @(
    (ConvertTo-WslPath $publishDir),
    (ConvertTo-WslPath $seedDir),
    (ConvertTo-WslPath $corpusDir),
    (ConvertTo-WslPath $crashDir),
    (ConvertTo-WslPath $dictFile),
    $MaxTotalTime, $MaxLen, $Timeout, $RssLimitMb
)
$runnerWsl = ConvertTo-WslPath $runnerSh

& wsl @wslPrefix -e bash $runnerWsl @args
$fuzzExit = $LASTEXITCODE

Write-Section 'Campaign finished'
$crashCount = (Get-ChildItem -File $crashDir -ErrorAction SilentlyContinue | Measure-Object).Count
$corpusCount = (Get-ChildItem -File $corpusDir -ErrorAction SilentlyContinue | Measure-Object).Count
Write-Host "libFuzzer exit code: $fuzzExit"
Write-Host "corpus units: $corpusCount"
Write-Host "crash artifacts: $crashCount  (in $crashDir)"
if ($crashCount -gt 0) {
    Write-Host ''
    Write-Host 'Findings were recorded. Reproduce one deterministically (no fuzzing loop) with:'
    Write-Host "  dotnet run --project `"$proj`" -- `"$crashDir`""
}

# A non-zero libFuzzer exit usually means a crash was found: surface it, but the
# campaign itself succeeded in running.
exit 0
