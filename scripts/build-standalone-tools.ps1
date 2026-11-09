[CmdletBinding()]
param()

# Build-only backstop for the standalone tool projects that KatLang.slnx deliberately omits.
# `validate-all.ps1 -Phase DotNet` builds the full solution, so a compile break in a project outside
# it (FrontEndStageProbe.cs called a removed resolver overload on 2026-11-08) goes unnoticed until
# someone runs the tool. This script compiles each listed project in Debug (`dotnet run --project`,
# as the seed commands of scripts/fuzz-parser.ps1 use it) and Release (the configuration the fuzz
# campaign publishes), since the harness has `#if DEBUG` code. It first checks that the list is
# exactly the tracked projects the solution omits, so a new standalone project cannot escape the
# check. It runs no tool and no test, is not a validation level, and does not change the
# `validate-all.ps1` phase contract.

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
$solution = "./KatLang.slnx"
# Every tracked project that KatLang.slnx omits, and why it stays outside:
# - fuzz/KatLang.ParserFuzz: the SharpFuzz harness; kept out so solution validation never depends
#   on it (see the csproj comment and fuzz/README.md "Layout").
$standaloneProjects = @(
    "fuzz/KatLang.ParserFuzz/KatLang.ParserFuzz.csproj"
)
$configurations = @("Debug", "Release")

function Initialize-Diagnostics {
    # A fresh directory under artifacts/validation/ once git confirms it is ignored, otherwise an
    # external temporary directory. Nothing existing is overwritten or deleted.
    $name = "standalone-tools-build-{0:yyyyMMddTHHmmssZ}-{1}" -f [DateTime]::UtcNow, $PID
    $relative = "artifacts/validation/$name"
    & git check-ignore -q -- "$relative/standalone-tools-build.log"
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
        Get-Content -LiteralPath $Path -Tail 60 | Out-Host
    }
}

# Returns the problems with the standalone list; empty when it is exactly the omitted projects.
function Test-StandaloneInventory {
    $tracked = @(& git ls-files -- "*.csproj" "*.fsproj" "*.vbproj")
    if ($LASTEXITCODE -ne 0) {
        return @("git ls-files exited with $LASTEXITCODE")
    }

    $inSolution = @((Select-String -LiteralPath $solution -Pattern 'Path="(?<path>[^"]+)"' -AllMatches).Matches |
        ForEach-Object { $_.Groups["path"].Value.Replace('\', '/') })
    $problems = @()
    foreach ($project in $tracked) {
        if ($project -notin $inSolution -and $project -notin $standaloneProjects) {
            $problems += "$project is tracked, outside $solution, and not listed in `$standaloneProjects"
        }
    }

    foreach ($project in $standaloneProjects) {
        if ($project -notin $tracked) {
            $problems += "$project is listed but is not a tracked project"
        }
        if ($project -in $inSolution) {
            $problems += "$project is listed but is already built as part of $solution"
        }
    }

    return $problems
}

# Native output goes to the log files, so the function's only pipeline output is its exit code.
function Invoke-StandaloneBuilds {
    param([Parameter(Mandatory = $true)][string]$Diagnostics)

    Write-Host "Diagnostics: $Diagnostics"
    Write-Host "==== Standalone project inventory ===="
    $problems = @(Test-StandaloneInventory)
    if ($problems.Count -gt 0) {
        foreach ($problem in $problems) {
            Write-Host "  $problem"
        }
        Write-Host "Standalone tool build FAILED: the standalone project list does not match the tracked projects outside $solution."
        return 1
    }
    Write-Host "  $($standaloneProjects.Count) standalone project(s): $($standaloneProjects -join ', ')"

    $built = 0
    foreach ($project in $standaloneProjects) {
        foreach ($configuration in $configurations) {
            $log = Join-Path $Diagnostics ("{0}-{1}.log" -f [System.IO.Path]::GetFileNameWithoutExtension($project), $configuration.ToLowerInvariant())
            Write-Host "==== Build $project ($configuration) ===="
            & dotnet build $project -c $configuration -p:UseSharedCompilation=false *> $log
            $buildExitCode = $LASTEXITCODE
            if ($buildExitCode -ne 0) {
                Write-LogTail -Path $log
                Write-Host "Standalone tool build FAILED: $project ($configuration) exited with $buildExitCode (full log: $log)."
                return $buildExitCode
            }
            $built++
        }
    }

    if ($built -ne $standaloneProjects.Count * $configurations.Count) {
        Write-Host "Standalone tool build FAILED: built $built of $($standaloneProjects.Count * $configurations.Count) project configuration(s)."
        return 1
    }

    Write-Host "Standalone tool build passed: $built project configuration(s) compiled."
    return 0
}

$exitCode = 1
Push-Location $repoRoot
try {
    $diagnostics = Initialize-Diagnostics
    $exitCode = Invoke-StandaloneBuilds -Diagnostics $diagnostics
}
finally {
    Pop-Location
}

exit $exitCode
