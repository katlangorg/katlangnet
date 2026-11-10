[CmdletBinding()]
param()

# Release-configuration backstop for the process-killing stack-overflow defect class.
# `validate-all.ps1` builds and tests in the default Debug configuration, but frame sizes are
# configuration-sensitive: S3's AstWalker overflow and the Batch 1 F1 deferred-compile overflow
# reproduced only (or much earlier) in Release. This script compiles the test project in Release
# and runs the focused stack suites below in Release. It fails when the build fails, a test fails,
# the filter executes nothing, or any listed class executes no test. It is not a validation level
# and does not replace a `validate-all.ps1` phase.

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
$project = "./tests/KatLang.Tests/KatLang.Tests.csproj"
# Fresh-process stack probes (SubprocessProbe children asserting exit code 0, a success marker and
# no "Stack overflow" text), plus the in-process async-twin stack-shape characterization, whose
# overflow would kill the test host. Every class must execute at least one test.
$stackSuiteClasses = @(
    "KatLang.Tests.AstStructuralDepthProcessTests",
    "KatLang.Tests.EvaluationLimitsProcessTests",
    "KatLang.Tests.ModelCStackProcessTests",
    "KatLang.Tests.DeferredCompileStackProcessTests",
    "KatLang.Tests.ExposureOpenChainDepthProcessTests",
    "KatLang.Tests.EvaluatorOpenChainStackProcessTests",
    "KatLang.Tests.StructuralNestingStackBackstopProcessTests",
    "KatLang.Tests.ClauseFamilyCompositionDepthProcessTests",
    "KatLang.Tests.AstGraphFuzzProcessTests",
    "KatLang.Tests.WeightedCostCompositionProcessTests",
    "KatLang.Tests.ScopeVisibilityIterativeUpdateTests",
    "KatLang.Tests.ParserExpressionChainDepthTests",
    "KatLang.Tests.LimitConfigurationTransparencyTests",
    "KatLang.Tests.AsyncEvaluation.AsyncStackDepthTests"
)
# The trailing dot matches only members of the named class, never a class whose name extends it.
$filter = ($stackSuiteClasses | ForEach-Object { "FullyQualifiedName~$_." }) -join "|"
$trxName = "stack-suites.trx"

function Initialize-Diagnostics {
    # A fresh directory under artifacts/validation/ once git confirms it is ignored, otherwise an
    # external temporary directory. Nothing existing is overwritten or deleted.
    $name = "stack-suites-release-{0:yyyyMMddTHHmmssZ}-{1}" -f [DateTime]::UtcNow, $PID
    $relative = "artifacts/validation/$name"
    & git check-ignore -q -- "$relative/stack-suites-build.log"
    $directory = if ($LASTEXITCODE -eq 0) {
        Join-Path $repoRoot $relative
    }
    else {
        Join-Path ([System.IO.Path]::GetTempPath()) "katlang-$name"
    }

    New-Item -ItemType Directory -Force -Path $directory | Out-Null
    return $directory
}

function Read-TrxResults {
    param([Parameter(Mandatory = $true)][string]$Path)

    if (-not (Test-Path -LiteralPath $Path)) {
        return @()
    }

    # A run that executed nothing writes a TRX without definitions or results; XPath reads that as empty.
    [xml]$trx = Get-Content -LiteralPath $Path -Raw
    $classes = @{}
    foreach ($method in @($trx.SelectNodes("//*[local-name()='UnitTest']/*[local-name()='TestMethod']"))) {
        $classes[$method.ParentNode.GetAttribute("id")] = $method.GetAttribute("className")
    }

    return @(@($trx.SelectNodes("//*[local-name()='UnitTestResult']")) | ForEach-Object {
        [pscustomobject]@{
            ClassName = $classes[$_.GetAttribute("testId")]
            Name = $_.GetAttribute("testName")
            Outcome = $_.GetAttribute("outcome")
        }
    })
}

function Write-LogTail {
    param([Parameter(Mandatory = $true)][string]$Path)

    if (Test-Path -LiteralPath $Path) {
        Get-Content -LiteralPath $Path -Tail 60 | Out-Host
    }
}

# Native output goes to the log files, so the function's only pipeline output is its exit code.
function Invoke-StackSuites {
    param([Parameter(Mandatory = $true)][string]$Diagnostics)

    $buildLog = Join-Path $Diagnostics "stack-suites-build.log"
    $testLog = Join-Path $Diagnostics "stack-suites-test.log"
    $resultsDirectory = Join-Path $Diagnostics "test-results"
    Write-Host "Diagnostics: $Diagnostics"

    Write-Host "==== Release build (fresh compile of the test project and its dependencies) ===="
    & dotnet build $project -c Release -p:UseSharedCompilation=false *> $buildLog
    $buildExitCode = $LASTEXITCODE
    if ($buildExitCode -ne 0) {
        Write-LogTail -Path $buildLog
        Write-Host "Release stack suites FAILED: build exited with $buildExitCode (full log: $buildLog)."
        return $buildExitCode
    }

    Write-Host "==== Release stack suites: $($stackSuiteClasses.Count) classes ===="
    & dotnet test $project -c Release -p:UseSharedCompilation=false --no-build `
        --filter $filter `
        --results-directory $resultsDirectory --logger "trx;LogFileName=$trxName" *> $testLog
    $testExitCode = $LASTEXITCODE

    # VSTest exits 0 when the filter matches nothing, so the executed tests are read from the TRX.
    $results = @(Read-TrxResults -Path (Join-Path $resultsDirectory $trxName))
    $notPassed = @($results | Where-Object { $_.Outcome -ne "Passed" })
    $missingClasses = @()
    foreach ($class in $stackSuiteClasses) {
        $classResults = @($results | Where-Object { $_.ClassName -eq $class })
        $classPassed = @($classResults | Where-Object { $_.Outcome -eq "Passed" }).Count
        Write-Host ("  {0}: {1} executed, {2} passed" -f $class, $classResults.Count, $classPassed)
        if ($classResults.Count -eq 0) {
            $missingClasses += $class
        }
    }
    Write-Host "Executed $($results.Count) test(s) in Release; $($notPassed.Count) not passed."
    foreach ($result in $notPassed) {
        Write-Host "  NOT PASSED ($($result.Outcome)): $($result.Name)"
    }

    if ($testExitCode -ne 0) {
        Write-LogTail -Path $testLog
        Write-Host "Release stack suites FAILED: dotnet test exited with $testExitCode (full log: $testLog)."
        return $testExitCode
    }

    if ($results.Count -eq 0) {
        Write-Host "Release stack suites FAILED: the filter executed no tests."
        return 1
    }

    if ($missingClasses.Count -gt 0) {
        Write-Host "Release stack suites FAILED: no test executed for $($missingClasses -join ', ')."
        return 1
    }

    if ($notPassed.Count -gt 0) {
        Write-Host "Release stack suites FAILED: $($notPassed.Count) test(s) did not pass."
        return 1
    }

    Write-Host "Release stack suites passed."
    return 0
}

$exitCode = 1
Push-Location $repoRoot
try {
    $diagnostics = Initialize-Diagnostics
    $exitCode = Invoke-StackSuites -Diagnostics $diagnostics
}
finally {
    Pop-Location
}

exit $exitCode
