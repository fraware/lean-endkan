# EndKan Deployment Guide

This document provides comprehensive instructions for deploying EndKan in various environments.

## Quick Start

### One-Command Installation

Choose your preferred method:

#### Docker (Recommended)
```bash
docker run --rm ghcr.io/fraware/lean-endkan:latest --help
```

#### Rust Package
```bash
cargo install endkan
endkan --help
```

#### Development Setup
```bash
# Linux/macOS
git clone https://github.com/fraware/lean-endkan.git
cd lean-endkan
make dev && make test

# Windows
git clone https://github.com/fraware/lean-endkan.git
cd lean-endkan
.\setup.ps1 dev && .\setup.ps1 test
```

## Deployment Methods

### 1. Docker Deployment

#### Single Container
```bash
# Pull and run
docker run --rm ghcr.io/fraware/lean-endkan:latest

# Build and run locally
git clone https://github.com/fraware/lean-endkan.git
cd lean-endkan
docker build -t endkan:latest .
docker run --rm endkan:latest
```

#### Docker Compose
```bash
# Production
docker-compose up

# Development with live reloading
docker-compose --profile dev up

# Testing
docker-compose --profile test up

# Benchmarking
docker-compose --profile benchmark up
```

### 2. Package Installation

#### Rust CLI Tool
```bash
# Install from crates.io
cargo install endkan

# Use immediately
endkan --help
endkan test
endkan benchmark
```

#### Lean Library
Add to your `Lakefile.lean`:
```lean
require lean-endkan from git "https://github.com/fraware/lean-endkan.git"
```

### 3. Source Deployment

#### Linux/macOS
```bash
# Clone repository
git clone https://github.com/fraware/lean-endkan.git
cd lean-endkan

# Automated setup
make dev

# Manual setup
elan toolchain install leanprover/lean4:v4.8.0
elan default leanprover/lean4:v4.8.0
lake update
lake build
cd rust_production && cargo build --release
```

#### Windows
```bash
# Clone repository
git clone https://github.com/fraware/lean-endkan.git
cd lean-endkan

# Automated setup
.\setup.ps1 dev

# Manual setup
powershell -Command "irm https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex"
elan toolchain install leanprover/lean4:v4.8.0
elan default leanprover/lean4:v4.8.0
lake update
lake build
cd rust_production && cargo build --release
```

## Production Deployment

### Environment Variables

```bash
# Performance tuning
export LEAN_TEST_TIMEOUT=30000
export LEAN_TEST_MEMORY_LIMIT=100000000
export LEAN_TEST_VERBOSE=true

# Rust logging
export RUST_LOG=info
```

### Docker Production Setup

```bash
# Build production image
docker build -t endkan:production .

# Run with production settings
docker run -d \
  --name endkan-prod \
  -p 8080:8080 \
  -e RUST_LOG=info \
  -e LEAN_TEST_VERBOSE=false \
  -v /data:/app/data \
  endkan:production
```

### Kubernetes Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: endkan
spec:
  replicas: 3
  selector:
    matchLabels:
      app: endkan
  template:
    metadata:
      labels:
        app: endkan
    spec:
      containers:
      - name: endkan
        image: ghcr.io/fraware/lean-endkan:latest
        ports:
        - containerPort: 8080
        env:
        - name: RUST_LOG
          value: "info"
        resources:
          requests:
            memory: "512Mi"
            cpu: "250m"
          limits:
            memory: "1Gi"
            cpu: "500m"
---
apiVersion: v1
kind: Service
metadata:
  name: endkan-service
spec:
  selector:
    app: endkan
  ports:
  - port: 80
    targetPort: 8080
  type: LoadBalancer
```

## CI/CD Integration

### GitHub Actions

The repository includes comprehensive CI/CD workflows:

- **Testing**: Multi-version testing with Lean 4.8.0, 4.9.0, 4.10.0
- **Quality**: Security, performance, and quality checks
- **Documentation**: Automatic documentation generation
- **Release**: Automated publishing to crates.io and Docker Hub

### Release Process

1. **Version Bump**: Update version in `rust_production/Cargo.toml`
2. **Push to Main**: CI automatically triggers release process
3. **Artifacts**: Docker images, Rust packages, and GitHub releases are created
4. **Verification**: All artifacts are tested before publication

### Dry Run Testing

```bash
# Test release process without publishing
DRY_RUN=true make release

# Test Docker build
docker build -t endkan:test .

# Test package build
cd rust_production && cargo build --release
```

## Monitoring and Maintenance

### Health Checks

```bash
# Docker health check
docker run --rm endkan:latest --help

# Application health
lake exe test

# Performance benchmarks
make benchmark
```

### Logging

```bash
# Enable verbose logging
export LEAN_TEST_VERBOSE=true
export RUST_LOG=debug

# Docker logging
docker logs endkan-container
```

### Performance Monitoring

```bash
# Run benchmarks
make benchmark

# Performance tests
lake exe run_production_tests

# Memory usage
docker stats endkan-container
```

## Troubleshooting

### Common Issues

1. **Lean Version Mismatch**
   ```bash
   elan toolchain install leanprover/lean4:v4.8.0
   elan default leanprover/lean4:v4.8.0
   ```

2. **Rust Build Failures**
   ```bash
   cd rust_production
   cargo clean
   cargo build --release
   ```

3. **Docker Build Issues**
   ```bash
   docker system prune -a
   docker build --no-cache -t endkan:latest .
   ```

4. **Memory Issues**
   ```bash
   export LEAN_TEST_MEMORY_LIMIT=2000000000
   ```

### Support

- **Documentation**: [README.md](README.md)
- **Issues**: [GitHub Issues](https://github.com/fraware/lean-endkan/issues)
- **Discussions**: [GitHub Discussions](https://github.com/fraware/lean-endkan/discussions)

## Security Considerations

### Container Security

```bash
# Run as non-root user
docker run --user 1000:1000 endkan:latest

# Read-only filesystem
docker run --read-only endkan:latest

# Resource limits
docker run --memory=1g --cpus=2 endkan:latest
```

### Network Security

```bash
# Internal networking only
docker run --network=internal endkan:latest

# TLS termination
docker run -p 443:8080 -v /certs:/certs endkan:latest
```

### Secrets Management

```bash
# Environment variables
docker run -e SECRET_KEY=value endkan:latest

# Secret mounts
docker run -v /secrets:/app/secrets:ro endkan:latest
```

## Performance Optimization

### Lean Compilation

```bash
# Parallel compilation
export LEAN_PARALLEL=4

# Memory optimization
export LEAN_MEMORY_LIMIT=2000000000
```

### Rust Optimization

```bash
# Release build with optimizations
cargo build --release

# Profile-guided optimization
cargo build --release --profile pgo
```

### Docker Optimization

```bash
# Multi-stage build optimization
docker build --target runtime .

# Layer caching
docker build --cache-from endkan:latest .
```

This deployment guide ensures that EndKan can be deployed reliably across all supported environments with optimal performance and security.
