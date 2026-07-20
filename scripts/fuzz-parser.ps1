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
#>
[CmdletBinding()]
param(
    [int]$MaxTotalTime = 600,    # total campaign wall-clock seconds
    [int]$MaxLen = 16384,        # max input length in bytes (16 KiB)
    [int]$Timeout = 5,           # per-input timeout in seconds
    [int]$RssLimitMb = 2048,     # memory limit (~2 GiB)
    [string]$Distro = '',        # optional specific WSL distro (else the WSL default)
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
$corpusDir  = Join-Path $fuzzDir 'artifacts\corpus'
$crashDir   = Join-Path $fuzzDir 'artifacts\crashes'
$seedDir    = Join-Path $fuzzDir 'KatLang.ParserFuzz\Testcases'
$dictFile   = Join-Path $fuzzDir 'katlang.dict'
$runnerSh   = Join-Path $fuzzDir 'run-campaign.sh'
$targetDll  = Join-Path $publishDir 'KatLang.dll'

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

Write-Section "Run libFuzzer in WSL ($MaxTotalTime s)"
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
