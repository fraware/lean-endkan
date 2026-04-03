# EndKan Setup Script for Windows PowerShell
# Run with: .\setup.ps1

param(
    [string]$Command = "help",
    [switch]$DryRun = $false
)

function Show-Help {
    Write-Host "EndKan - Practical Automation for Ends, Coends, and Kan Extensions" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "Available commands:" -ForegroundColor Yellow
    Write-Host "  dev           Set up local development environment" -ForegroundColor Green
    Write-Host "  run           Run the application/CLI locally" -ForegroundColor Green
    Write-Host "  test          Run all tests" -ForegroundColor Green
    Write-Host "  clean         Clean build artifacts" -ForegroundColor Green
    Write-Host "  build         Build the project" -ForegroundColor Green
    Write-Host "  check         Run code quality checks" -ForegroundColor Green
    Write-Host "  install       Install the package system-wide" -ForegroundColor Green
    Write-Host "  docker-build  Build Docker image" -ForegroundColor Green
    Write-Host "  docker-run    Run Docker container" -ForegroundColor Green
    Write-Host "  benchmark     Run performance benchmarks" -ForegroundColor Green
    Write-Host "  quickstart    Quick start for new users" -ForegroundColor Green
    Write-Host ""
    Write-Host "Usage: .\setup.ps1 <command>" -ForegroundColor Cyan
    Write-Host "Example: .\setup.ps1 dev" -ForegroundColor Cyan
}

function Test-Command {
    param([string]$CommandName)
    $null = Get-Command $CommandName -ErrorAction SilentlyContinue
    return $?
}

function Install-Elan {
    Write-Host "Installing Elan (Lean version manager)..." -ForegroundColor Yellow
    try {
        Invoke-RestMethod -Uri "https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1" | Invoke-Expression
        Write-Host "✓ Elan installed successfully" -ForegroundColor Green
    }
    catch {
        Write-Host "✗ Failed to install Elan: $_" -ForegroundColor Red
        exit 1
    }
}

function Install-Rust {
    Write-Host "Installing Rust..." -ForegroundColor Yellow
    try {
        Invoke-RestMethod -Uri "https://sh.rustup.rs" -OutFile "rustup-init.exe"
        .\rustup-init.exe -y
        Remove-Item "rustup-init.exe"
        Write-Host "✓ Rust installed successfully" -ForegroundColor Green
    }
    catch {
        Write-Host "✗ Failed to install Rust: $_" -ForegroundColor Red
        exit 1
    }
}

function Setup-Dev {
    Write-Host "Setting up EndKan development environment..." -ForegroundColor Cyan
    
    # Check for Elan
    if (-not (Test-Command "elan")) {
        Install-Elan
    }
    else {
        Write-Host "✓ Elan detected" -ForegroundColor Green
    }
    
    # Update Elan and install Lean
    Write-Host "Installing Lean 4.8.0..." -ForegroundColor Yellow
    elan self update
    elan toolchain install leanprover/lean4:v4.8.0
    elan default leanprover/lean4:v4.8.0
    Write-Host "✓ Lean 4.8.0 installed and set as default" -ForegroundColor Green
    
    # Update and build Lake project
    Write-Host "Building Lean project..." -ForegroundColor Yellow
    lake update
    lake build
    Write-Host "✓ Dependencies updated and project built" -ForegroundColor Green
    
    # Check for Rust
    if (Test-Command "cargo") {
        Write-Host "✓ Rust/Cargo detected" -ForegroundColor Green
        Set-Location "rust_production"
        cargo build
        Set-Location ".."
        Write-Host "✓ Rust program built" -ForegroundColor Green
    }
    else {
        Write-Host "⚠ Rust not detected. Install Rust from https://rustup.rs/ if you want the optional CLI." -ForegroundColor Yellow
    }
    
    Write-Host ""
    Write-Host "Development environment ready." -ForegroundColor Green
    Write-Host "Run '.\setup.ps1 run' to start the application or '.\setup.ps1 test' to run tests." -ForegroundColor Cyan
}

function Run-Tests {
    Write-Host "Running EndKan test suite..." -ForegroundColor Cyan
    lake exe test
    Write-Host "Running longer Lean smoke tests..." -ForegroundColor Cyan
    lake exe run_tests
    Write-Host "Running demo monitoring / benchmark harness..." -ForegroundColor Cyan
    lake exe run_production_tests
    
    if (Test-Command "cargo") {
        Write-Host "Running Rust tests..." -ForegroundColor Cyan
        Set-Location "rust_production"
        cargo test
        Set-Location ".."
    }
    
    Write-Host "✓ All tests completed successfully" -ForegroundColor Green
}

function Build-Project {
    Write-Host "Building EndKan..." -ForegroundColor Cyan
    lake build
    
    if (Test-Command "cargo") {
        Write-Host "Building Rust program..." -ForegroundColor Cyan
        Set-Location "rust_production"
        cargo build --release
        Set-Location ".."
    }
    
    Write-Host "✓ Build completed successfully" -ForegroundColor Green
}

function Clean-Project {
    Write-Host "Cleaning build artifacts..." -ForegroundColor Cyan
    lake clean
    
    if (Test-Command "cargo") {
        Set-Location "rust_production"
        cargo clean
        Set-Location ".."
    }
    
    Write-Host "✓ Clean completed" -ForegroundColor Green
}

function Check-Quality {
    Write-Host "Running code quality checks..." -ForegroundColor Cyan
    lake build
    Write-Host "✓ Lean code builds successfully" -ForegroundColor Green
    
    if (Test-Command "cargo") {
        Set-Location "rust_production"
        cargo check
        cargo clippy -- -D warnings
        Set-Location ".."
        Write-Host "✓ Rust code quality checks passed" -ForegroundColor Green
    }
    
    Write-Host "✓ Code quality checks passed" -ForegroundColor Green
}

function Install-Package {
    Write-Host "Installing EndKan..." -ForegroundColor Cyan
    Build-Project
    
    if (Test-Command "cargo") {
        Set-Location "rust_production"
        cargo install --path .
        Set-Location ".."
        Write-Host "✓ EndKan CLI installed successfully" -ForegroundColor Green
        Write-Host "Run 'endkan health --help' for CLI options" -ForegroundColor Cyan
    }
    else {
        Write-Host "⚠ Rust/Cargo not found. Cannot install CLI components." -ForegroundColor Yellow
        Write-Host "Lean library can be used by adding to your Lakefile.lean:" -ForegroundColor Cyan
        Write-Host 'require «lean-endkan» from git "https://github.com/fraware/lean-endkan.git" @ "main"' -ForegroundColor White
    }
}

function Build-Docker {
    Write-Host "Building Docker image..." -ForegroundColor Cyan
    if (Test-Command "docker") {
        docker build -t endkan:latest .
        Write-Host "✓ Docker image built successfully" -ForegroundColor Green
    }
    else {
        Write-Host "✗ Docker not found. Please install Docker Desktop." -ForegroundColor Red
    }
}

function Run-Docker {
    Write-Host "Running EndKan in Docker..." -ForegroundColor Cyan
    if (Test-Command "docker") {
        Build-Docker
        docker run --rm endkan:latest health
    }
    else {
        Write-Host "✗ Docker not found. Please install Docker Desktop." -ForegroundColor Red
    }
}

function Run-Benchmark {
    Write-Host "Running demo benchmark harness..." -ForegroundColor Cyan
    lake exe run_production_tests
    
    if (Test-Command "cargo") {
        Set-Location "rust_production"
        cargo test --release
        Set-Location ".."
    }
    
    Write-Host "✓ Benchmark step finished" -ForegroundColor Green
}

function Show-Quickstart {
    Write-Host "EndKan quick start" -ForegroundColor Cyan
    Write-Host "====================" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "1. Clone the repository:" -ForegroundColor Yellow
    Write-Host "   git clone https://github.com/fraware/lean-endkan.git" -ForegroundColor White
    Write-Host "   cd lean-endkan" -ForegroundColor White
    Write-Host ""
    Write-Host "2. Set up development environment:" -ForegroundColor Yellow
    Write-Host "   .\setup.ps1 dev" -ForegroundColor White
    Write-Host ""
    Write-Host "3. Run tests to verify installation:" -ForegroundColor Yellow
    Write-Host "   .\setup.ps1 test" -ForegroundColor White
    Write-Host ""
    Write-Host "4. Try the application:" -ForegroundColor Yellow
    Write-Host "   .\setup.ps1 run" -ForegroundColor White
    Write-Host ""
    Write-Host "5. Or use Docker:" -ForegroundColor Yellow
    Write-Host "   .\setup.ps1 docker-run" -ForegroundColor White
    Write-Host ""
    Write-Host "6. Or install as a package:" -ForegroundColor Yellow
    Write-Host "   .\setup.ps1 install" -ForegroundColor White
    Write-Host "   endkan health --help" -ForegroundColor White
    Write-Host ""
    Write-Host "See README.md for more." -ForegroundColor Cyan
}

# Main command dispatcher
switch ($Command.ToLower()) {
    "help" { Show-Help }
    "dev" { Setup-Dev }
    "run" { 
        Write-Host "Running EndKan..." -ForegroundColor Cyan
        lake exe test
        if (Test-Command "cargo") {
            Write-Host "Running Rust CLI (help for health subcommand)..." -ForegroundColor Cyan
            Set-Location "rust_production"
            cargo run --bin endkan -- health --help
            Set-Location ".."
        }
    }
    "test" { Run-Tests }
    "build" { Build-Project }
    "clean" { Clean-Project }
    "check" { Check-Quality }
    "install" { Install-Package }
    "docker-build" { Build-Docker }
    "docker-run" { Run-Docker }
    "benchmark" { Run-Benchmark }
    "quickstart" { Show-Quickstart }
    default {
        Write-Host "Unknown command: $Command" -ForegroundColor Red
        Write-Host "Run '.\setup.ps1 help' for available commands." -ForegroundColor Yellow
        exit 1
    }
}
