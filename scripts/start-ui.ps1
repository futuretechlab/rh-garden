$ErrorActionPreference = "Stop"
$projectRoot = Split-Path -Parent $PSScriptRoot

Push-Location $projectRoot
try {
  cabal run rh-garden -- ui-export
  Push-Location (Join-Path $projectRoot "ui")
  try {
    npm run dev
  }
  finally {
    Pop-Location
  }
}
finally {
  Pop-Location
}
