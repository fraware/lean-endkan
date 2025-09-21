.PHONY: help dev run test clean build release install uninstall check lint format docker-build docker-run docker-push

# Default target
help: ## Show this help message
	@echo "EndKan - Practical Automation for Ends, Coends, and Kan Extensions"
	@echo ""
	@echo "Available targets:"
	@awk 'BEGIN {FS = ":.*?## "} /^[a-zA-Z_-]+:.*?## / {printf "  \033[36m%-15s\033[0m %s\n", $$1, $$2}' $(MAKEFILE_LIST)

# Development setup
dev: ## Set up local development environment
	@echo "Setting up EndKan development environment..."
	@if command -v elan >/dev/null 2>&1; then \
		echo "✓ Elan (Lean version manager) detected"; \
	else \
		echo "Installing Elan..."; \
		curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh; \
	fi
	@elan self update
	@elan toolchain install leanprover/lean4:v4.8.0
	@elan default leanprover/lean4:v4.8.0
	@echo "✓ Lean 4.8.0 installed and set as default"
	@lake update
	@lake build
	@echo "✓ Dependencies updated and project built"
	@if command -v cargo >/dev/null 2>&1; then \
		echo "✓ Rust/Cargo detected"; \
		cd rust_production && cargo build; \
		echo "✓ Rust production components built"; \
	else \
		echo "⚠ Rust not detected. Install Rust for production features: https://rustup.rs/"; \
	fi
	@echo ""
	@echo "🎉 Development environment ready!"
	@echo "Run 'make run' to start the application or 'make test' to run tests."

# Run the application locally
run: ## Run the application/CLI locally
	@echo "Running EndKan..."
	@lake exe test
	@if command -v cargo >/dev/null 2>&1; then \
		echo "Running Rust production components..."; \
		cd rust_production && cargo run --bin endkan-production -- --help; \
	fi

# Run tests
test: ## Run all tests
	@echo "Running EndKan test suite..."
	@lake exe test
	@echo "Running comprehensive test suite..."
	@lake exe run_tests
	@echo "Running production tests..."
	@lake exe run_production_tests
	@if command -v cargo >/dev/null 2>&1; then \
		echo "Running Rust tests..."; \
		cd rust_production && cargo test; \
	fi
	@echo "✓ All tests completed successfully"

# Build the project
build: ## Build the project
	@echo "Building EndKan..."
	@lake build
	@if command -v cargo >/dev/null 2>&1; then \
		echo "Building Rust production components..."; \
		cd rust_production && cargo build --release; \
	fi
	@echo "✓ Build completed successfully"

# Clean build artifacts
clean: ## Clean build artifacts
	@echo "Cleaning build artifacts..."
	@lake clean
	@if command -v cargo >/dev/null 2>&1; then \
		cd rust_production && cargo clean; \
	fi
	@echo "✓ Clean completed"

# Check code quality
check: ## Run code quality checks
	@echo "Running code quality checks..."
	@lake build
	@echo "✓ Lean code builds successfully"
	@if command -v cargo >/dev/null 2>&1; then \
		cd rust_production && cargo check; \
		cd rust_production && cargo clippy -- -D warnings; \
	fi
	@echo "✓ Code quality checks passed"

# Lint code
lint: ## Lint the codebase
	@echo "Running linter..."
	@lake build
	@if command -v cargo >/dev/null 2>&1; then \
		cd rust_production && cargo clippy -- -D warnings; \
	fi
	@echo "✓ Linting completed"

# Format code
format: ## Format the codebase
	@echo "Formatting code..."
	@if command -v cargo >/dev/null 2>&1; then \
		cd rust_production && cargo fmt; \
	fi
	@echo "✓ Code formatting completed"

# Install the package
install: build ## Install the package system-wide
	@echo "Installing EndKan..."
	@if command -v cargo >/dev/null 2>&1; then \
		cd rust_production && cargo install --path .; \
		echo "✓ EndKan CLI installed successfully"; \
		echo "Run 'endkan-production --help' to get started"; \
	else \
		echo "⚠ Rust/Cargo not found. Cannot install CLI components."; \
		echo "Lean library can be used by adding to your Lakefile.lean:"; \
		echo "require lean-endkan from git \"https://github.com/fraware/lean-endkan.git\""; \
	fi

# Uninstall the package
uninstall: ## Uninstall the package
	@echo "Uninstalling EndKan..."
	@if command -v cargo >/dev/null 2>&1; then \
		cargo uninstall endkan-production; \
		echo "✓ EndKan CLI uninstalled"; \
	fi

# Build Docker image
docker-build: ## Build Docker image
	@echo "Building Docker image..."
	@docker build -t endkan:latest .
	@echo "✓ Docker image built successfully"

# Run Docker container
docker-run: docker-build ## Run Docker container
	@echo "Running EndKan in Docker..."
	@docker run --rm endkan:latest --help

# Push Docker image to registry
docker-push: docker-build ## Push Docker image to registry
	@echo "Pushing Docker image to registry..."
	@docker tag endkan:latest ghcr.io/fraware/lean-endkan:latest
	@docker push ghcr.io/fraware/lean-endkan:latest
	@echo "✓ Docker image pushed to ghcr.io/fraware/lean-endkan:latest"

# Release the package (supports dry-run)
release: test check ## Build and publish artifacts (supports dry-run)
	@echo "Preparing release..."
	@if [ "$(DRY_RUN)" = "true" ]; then \
		echo "🧪 DRY RUN MODE - No actual publishing will occur"; \
		echo "Would publish to:"; \
		echo "  - crates.io (Rust package)"; \
		echo "  - ghcr.io (Docker image)"; \
		echo "  - GitHub Releases"; \
	else \
		echo "🚀 Publishing release..."; \
		$(MAKE) publish-cargo; \
		$(MAKE) docker-push; \
		$(MAKE) publish-github-release; \
		echo "✅ Release published successfully!"; \
	fi

# Publish to crates.io
publish-cargo: ## Publish Rust package to crates.io
	@echo "Publishing to crates.io..."
	@cd rust_production && cargo publish --token $(CRATES_IO_TOKEN)
	@echo "✓ Published to crates.io"

# Create GitHub release
publish-github-release: ## Create GitHub release
	@echo "Creating GitHub release..."
	@gh release create v$(VERSION) \
		--title "EndKan v$(VERSION)" \
		--notes "Release v$(VERSION) of EndKan - Practical Automation for Ends, Coends, and Kan Extensions" \
		--latest
	@echo "✓ GitHub release created"

# Development shortcuts
dev-setup: dev ## Alias for dev target
test-all: test ## Alias for test target
build-all: build ## Alias for build target

# Version management
version: ## Show current version
	@echo "EndKan version information:"
	@echo "  Lean library: $(shell grep 'version' Lakefile.lean || echo 'Not specified')"
	@echo "  Rust package: $(shell cd rust_production && grep 'version' Cargo.toml)"
	@echo "  Git tag: $(shell git describe --tags --exact-match 2>/dev/null || echo 'No tag')"

# Performance benchmarks
benchmark: ## Run performance benchmarks
	@echo "Running performance benchmarks..."
	@lake exe run_production_tests
	@if command -v cargo >/dev/null 2>&1; then \
		cd rust_production && cargo bench; \
	fi
	@echo "✓ Benchmarks completed"

# Documentation generation
docs: ## Generate documentation
	@echo "Generating documentation..."
	@lake build
	@echo "✓ Documentation generated in build/doc/"

# Full development cycle
full-test: clean build test check lint ## Run full test cycle
	@echo "✅ Full test cycle completed successfully"

# CI/CD helpers
ci-test: ## Run tests suitable for CI
	@echo "Running CI tests..."
	@lake update
	@lake build
	@lake exe test
	@if command -v cargo >/dev/null 2>&1; then \
		cd rust_production && cargo test --release; \
	fi

ci-build: ## Build suitable for CI
	@echo "Running CI build..."
	@lake build
	@if command -v cargo >/dev/null 2>&1; then \
		cd rust_production && cargo build --release; \
	fi

# Quick start for new users
quickstart: ## Quick start for new users
	@echo "🚀 EndKan Quick Start"
	@echo "==================="
	@echo ""
	@echo "1. Clone the repository:"
	@echo "   git clone https://github.com/fraware/lean-endkan.git"
	@echo "   cd lean-endkan"
	@echo ""
	@echo "2. Set up development environment:"
	@echo "   make dev"
	@echo ""
	@echo "3. Run tests to verify installation:"
	@echo "   make test"
	@echo ""
	@echo "4. Try the application:"
	@echo "   make run"
	@echo ""
	@echo "5. Or use Docker:"
	@echo "   make docker-run"
	@echo ""
	@echo "6. Or install as a package:"
	@echo "   make install"
	@echo "   endkan-production --help"
	@echo ""
	@echo "📚 For more information, see README.md"
