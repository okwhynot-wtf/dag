# DAG VERIFY (Windows PowerShell)
$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot
Write-Host "== DAG VERIFY =="

function Invoke-LakeBuild([string]$dir) {
  Push-Location $dir
  try {
    lake build
    if ($LASTEXITCODE -ne 0) { throw "lake build failed in $dir (exit $LASTEXITCODE)" }
  } finally {
    Pop-Location
  }
}

Invoke-LakeBuild "formal\spine"
Invoke-LakeBuild "formal\ledger"
Invoke-LakeBuild "formal\bridge"
Invoke-LakeBuild "formal\dictionary"
Invoke-LakeBuild "formal\experimental"

python exhibits\quintom\integrate.py
if ($LASTEXITCODE -ne 0) { throw "quintom exhibit failed" }

python exhibits\wave\periods.py
if ($LASTEXITCODE -ne 0) { throw "wave period exhibit failed" }

Write-Host "== DAG VERIFY OK =="
