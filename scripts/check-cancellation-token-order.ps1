[CmdletBinding()]
param()

# Early pre-V3 contract check: every C# parameter list of the KatLang assembly ends with its
# CancellationTokens (`CancellationTokenParameterOrderTests`, the authoritative reflection scan).
# Run it right after changing any method or constructor signature, before feature tests and
# long before V3. It compiles the current sources, runs the whole test class, and fails when
# the build fails, a test fails, or the filter executes nothing.

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
$project = "./tests/KatLang.Tests/KatLang.Tests.csproj"
$testClass = "KatLang.Tests.CancellationTokenParameterOrderTests"
# The scan itself; the class's other test proves the scan detects violations.
$requiredTest = "$testClass.EveryParameterListOfTheKatLangAssembly_EndsWithItsCancellationTokens"
$resultsDirectory = Join-Path ([System.IO.Path]::GetTempPath()) "katlang-ct-order-$([guid]::NewGuid().ToString('N'))"

function Read-TrxResults {
    param([Parameter(Mandatory = $true)][string]$Path)

    if (-not (Test-Path -LiteralPath $Path)) {
        return @()
    }

    # A run that executed nothing writes a TRX without definitions or results; XPath reads that as empty.
    [xml]$trx = Get-Content -LiteralPath $Path -Raw
    $names = @{}
    foreach ($method in @($trx.SelectNodes("//*[local-name()='UnitTest']/*[local-name()='TestMethod']"))) {
        $names[$method.ParentNode.GetAttribute("id")] = "$($method.GetAttribute('className')).$($method.GetAttribute('name'))"
    }

    return @(@($trx.SelectNodes("//*[local-name()='UnitTestResult']")) | ForEach-Object {
        [pscustomobject]@{ Name = $names[$_.GetAttribute("testId")]; Outcome = $_.GetAttribute("outcome") }
    })
}

# Native output goes to the host, so the function's only pipeline output is its exit code.
function Invoke-OrderCheck {
    Write-Host "==== Build (fresh compile of the test project and its dependencies) ===="
    & dotnet build $project -p:UseSharedCompilation=false | Out-Host
    if ($LASTEXITCODE -ne 0) {
        Write-Host "CancellationToken-order check FAILED: build exited with $LASTEXITCODE."
        return $LASTEXITCODE
    }

    Write-Host "==== $testClass ===="
    & dotnet test $project -p:UseSharedCompilation=false --no-build `
        --filter "FullyQualifiedName~$testClass" `
        --results-directory $resultsDirectory --logger "trx;LogFileName=ct-order.trx" | Out-Host
    $testExitCode = $LASTEXITCODE

    # VSTest exits 0 when the filter matches nothing, so the executed tests are read from the TRX.
    $results = @(Read-TrxResults -Path (Join-Path $resultsDirectory "ct-order.trx"))
    $notPassed = @($results | Where-Object { $_.Outcome -ne "Passed" })
    $requiredPassed = @($results | Where-Object { $_.Name -eq $requiredTest -and $_.Outcome -eq "Passed" }).Count -eq 1
    Write-Host "Executed $($results.Count) test(s) of $testClass; $($notPassed.Count) not passed."

    if ($testExitCode -ne 0) {
        Write-Host "CancellationToken-order check FAILED: dotnet test exited with $testExitCode (violations are listed above)."
        return $testExitCode
    }

    if ($results.Count -eq 0) {
        Write-Host "CancellationToken-order check FAILED: the filter executed no tests."
        return 1
    }

    if ($notPassed.Count -gt 0 -or -not $requiredPassed) {
        Write-Host "CancellationToken-order check FAILED: $requiredTest did not run and pass."
        return 1
    }

    Write-Host "CancellationToken-order check passed."
    return 0
}

$exitCode = 1
Push-Location $repoRoot
try {
    $exitCode = Invoke-OrderCheck
}
finally {
    Pop-Location
    if (Test-Path -LiteralPath $resultsDirectory) {
        Remove-Item -LiteralPath $resultsDirectory -Recurse -Force
    }
}

exit $exitCode
