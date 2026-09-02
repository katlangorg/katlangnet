[CmdletBinding()]
param(
    [AllowEmptyString()]
    [string]$RequestedVersion
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

function Test-ReleaseVersion {
    param([Parameter(Mandatory = $true)][string]$Version)

    if ($Version -notmatch '^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(?:-([0-9A-Za-z.-]+))?$') {
        return $false
    }

    if ([string]::IsNullOrEmpty($Matches[4])) {
        return $true
    }

    foreach ($identifier in $Matches[4].Split('.')) {
        if ($identifier.Length -eq 0) {
            return $false
        }

        if ($identifier -match '^[0-9]+$' -and $identifier.Length -gt 1 -and $identifier[0] -eq '0') {
            return $false
        }
    }

    return $true
}

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
$propsPath = Join-Path $repoRoot "KatLangVersion.props"

if (-not (Test-Path -LiteralPath $propsPath -PathType Leaf)) {
    throw "KatLangVersion.props is missing at the repository root."
}

[xml]$props = Get-Content -LiteralPath $propsPath -Raw
$versionNodes = @($props.SelectNodes('/Project/PropertyGroup/KatLangVersion'))
if ($versionNodes.Count -ne 1) {
    throw "KatLangVersion.props must contain exactly one <KatLangVersion>; found $($versionNodes.Count)."
}

$repositoryVersion = $versionNodes[0].InnerText.Trim()
if (-not (Test-ReleaseVersion -Version $repositoryVersion)) {
    throw "KatLangVersion.props contains an invalid release version: '$repositoryVersion'."
}

if ($PSBoundParameters.ContainsKey('RequestedVersion')) {
    if (-not (Test-ReleaseVersion -Version $RequestedVersion)) {
        throw "Requested version is malformed or unsafe: '$RequestedVersion'. Enter a semantic version without the v prefix."
    }

    if ($RequestedVersion -cne $repositoryVersion) {
        throw "Requested version '$RequestedVersion' does not match repository version '$repositoryVersion'."
    }
}

Write-Output $repositoryVersion
