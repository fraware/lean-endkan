# EndKan acceptance matrix (Phase 5 optional gate).
# Requires: elan/lake on PATH, repo root as cwd or any descendant.
# Exit code: 0 when all steps pass, 1 on first failure.

$ErrorActionPreference = "Stop"
# Lake writes linter warnings to stderr; do not treat them as terminating errors.
$PSNativeCommandUseErrorActionPreference = $false

function Invoke-Step {
    param(
        [string]$Name,
        [scriptblock]$Action
    )
    Write-Host ""
    Write-Host "== $Name =="
    $prevErrorAction = $ErrorActionPreference
    $ErrorActionPreference = "Continue"
    $output = & $Action 2>&1
    $exitCode = $LASTEXITCODE
    $ErrorActionPreference = $prevErrorAction
    $output | Out-Host
    if ($exitCode -ne 0) {
        Write-Error "$Name failed (exit $exitCode)"
        exit 1
    }
}

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
Set-Location $repoRoot

Write-Host "EndKan acceptance matrix"
Write-Host "Repository: $repoRoot"
Write-Host "Toolchain:  $(Get-Content -Raw lean-toolchain)"

Invoke-Step "lake build EndKan" { lake build EndKan }
Invoke-Step "lake build Scratch.SliceIsoMin" { lake build Scratch.SliceIsoMin }
Invoke-Step "lake build Scratch.MathlibFubiniExamples" { lake build Scratch.MathlibFubiniExamples }
Invoke-Step "lake build Scratch.MathlibKanBcExamples" { lake build Scratch.MathlibKanBcExamples }
Invoke-Step "lake env lean scratch/SliceIsoMin.lean" { lake env lean scratch/SliceIsoMin.lean }
Invoke-Step "lake exe test" { lake exe test }
Invoke-Step "lake exe run_tests" { lake exe run_tests }
Invoke-Step "lake exe test-runner" { lake exe test-runner }

Write-Host ""
Write-Host "All acceptance steps passed."
