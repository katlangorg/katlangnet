# Derives the three Evaluator.cs mutation ranges in stryker-config.json from the
# file's stable region banners, and validates that the known mutation-campaign
# sites fall inside the intended ranges (see docs/design/mutation-campaign-2026-08.md).
#
# Stryker.NET mutate spans are CHARACTER offsets (UTF-16 code units, CRLF = 2)
# into the on-disk file. Each range runs from the start of its opening banner
# line to the start of its closing banner line, so both boundaries sit inside
# comment/blank text and never cut a mutant:
#   1. "// ── Bind parameters"   .. "// ── Result helpers"                    (parameter/call-argument binding)
#   2. "// ── Pattern matching"  .. "// ── Collection materialization budget" (parameter-pattern matching)
#   3. "// ── Main eval"         .. "// ── Entry points"                      (evaluation, calls, dot-calls)
#
# Usage:
#   pwsh ./scripts/compute-stryker-offsets.ps1           # print + validate
#   pwsh ./scripts/compute-stryker-offsets.ps1 -Update   # also rewrite stryker-config.json
param([switch]$Update)

$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent $PSScriptRoot
$evaluatorPath = Join-Path $repoRoot 'src/KatLang/Evaluator.cs'
$configPath = Join-Path $repoRoot 'stryker-config.json'
$text = [System.IO.File]::ReadAllText($evaluatorPath)

function Find-UniqueIndex([string]$needle) {
    $first = $text.IndexOf($needle, [System.StringComparison]::Ordinal)
    if ($first -lt 0) { throw "Anchor not found in Evaluator.cs: '$needle'" }
    if ($text.IndexOf($needle, $first + 1, [System.StringComparison]::Ordinal) -ge 0) {
        throw "Anchor is not unique in Evaluator.cs: '$needle'"
    }
    return $first
}

function Get-LineStart([int]$index) { return $text.LastIndexOf("`n", $index) + 1 }
function Get-LineNumber([int]$index) {
    $line = 1
    for ($i = 0; $i -lt $index; $i++) { if ($text[$i] -eq "`n") { $line++ } }
    return $line
}

$regions = foreach ($anchor in @(
        @{ Name = 'bind-parameters';  Open = '// ── Bind parameters ';  Close = '// ── Result helpers ' },
        @{ Name = 'pattern-matching'; Open = '// ── Pattern matching '; Close = '// ── Collection materialization budget ' },
        @{ Name = 'eval-call-dotcall'; Open = '// ── Main eval ';        Close = '// ── Entry points ' })) {
    $start = Get-LineStart (Find-UniqueIndex $anchor.Open)
    $end = Get-LineStart (Find-UniqueIndex $anchor.Close)
    if ($end -le $start) { throw "Range '$($anchor.Name)' is inverted." }
    [pscustomobject]@{ Name = $anchor.Name; Start = $start; End = $end }
}

foreach ($region in $regions) {
    $startLine = Get-LineNumber $region.Start
    $endLine = Get-LineNumber $region.End
    Write-Host ("{0}: chars {1}..{2} (lines {3}..{4})" -f $region.Name, $region.Start, $region.End, $startLine, $endLine)
}
$mutatePattern = '**/Evaluator.cs' + (($regions | ForEach-Object { '{' + $_.Start + '..' + $_.End + '}' }) -join '')
Write-Host "mutate entry: $mutatePattern"

# ── Validate that the known campaign sites are inside the intended ranges ──
function Assert-InRegion([string]$needle, [int]$regionIndex, [int]$occurrence = 0) {
    $index = -1
    for ($seen = 0; $seen -le $occurrence; $seen++) {
        $index = $text.IndexOf($needle, $index + 1, [System.StringComparison]::Ordinal)
        if ($index -lt 0) { throw "Site occurrence $occurrence not found: '$needle'" }
    }
    $region = $regions[$regionIndex]
    if ($index -lt $region.Start -or $index -ge $region.End) {
        throw "Site '$needle' (occurrence $occurrence, char $index, line $(Get-LineNumber $index)) is OUTSIDE region '$($region.Name)'."
    }
    Write-Host ("  ok: {0} (occurrence {1}) in {2}, line {3}" -f $needle.Substring(0, [Math]::Min(58, $needle.Length)), $occurrence, $region.Name, (Get-LineNumber $index))
}

Write-Host 'validating known campaign sites:'
# G12 flat suffix arithmetic (BindCallableArguments)
Assert-InRegion 'var parameterIndex = collectingIndex + 1 + suffixIndex;' 0
# G12 suffix loops: occurrence 0 = plain BindParameterPatternList (region 1),
# occurrence 1 = counted BindCountedParameterPatternList (region 2)
Assert-InRegion 'BindOne(collectingIndex + 1 + suffixIndex, suffixInputStart + suffixIndex);' 0 0
Assert-InRegion 'BindOne(collectingIndex + 1 + suffixIndex, suffixInputStart + suffixIndex);' 1 1
# G13 eager-parameter resource-limit retention policy
Assert-InRegion 'internal static EvalError? RetainResourceLimitForAlgorithmBinding' 0
# G14 prepared-argument boundary policy
Assert-InRegion 'internal static CountedResult PrepareCallArgumentBoundaryCount' 0
# G15 Decimal128 edges
Assert-InRegion 'internal static int ClampRoundDigits' 2
Assert-InRegion 'internal static Decimal128 CanonicalizeMathResult' 2
Assert-InRegion 'internal static Decimal128 SampleRandomUnitFraction' 2
Assert-InRegion 'internal static Decimal128 ScaleRandomUnitFractionToHalfOpenRange' 2
Assert-InRegion 'internal static UInt128 NextRandomUInt128' 2
Assert-InRegion 'internal static Decimal128 SampleUniformInteger' 2
Assert-InRegion 'Math.Random bounds must be finite numbers' 2
Assert-InRegion 'Math.RandomInt bounds must not exceed 1e34 in magnitude' 2

if ($Update) {
    $config = [System.IO.File]::ReadAllText($configPath)
    $pattern = '\*\*/Evaluator\.cs(\{\d+\.\.\d+\})+'
    if ($config -notmatch $pattern) { throw 'Evaluator.cs mutate entry not found in stryker-config.json.' }
    $updated = [System.Text.RegularExpressions.Regex]::Replace($config, $pattern, $mutatePattern.Replace('**/', '**/'))
    [System.IO.File]::WriteAllText($configPath, $updated)
    $null = (Get-Content $configPath -Raw | ConvertFrom-Json)  # must stay valid JSON
    Write-Host "stryker-config.json updated and re-validated as JSON."
}