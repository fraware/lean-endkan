# Multi-stage Dockerfile for EndKan
# Stage 1: Build environment
FROM ubuntu:22.04 as builder

# Install system dependencies
RUN apt-get update && apt-get install -y \
    curl \
    build-essential \
    git \
    && rm -rf /var/lib/apt/lists/*

# Install Elan (Lean version manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
ENV PATH="/root/.elan/bin:$PATH"

# Install Lean 4.8.0
RUN elan toolchain install leanprover/lean4:v4.8.0
RUN elan default leanprover/lean4:v4.8.0

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:$PATH"

# Set working directory
WORKDIR /app

# Copy project files
COPY . .

# Build Lean project
RUN lake update
RUN lake build

# Build Rust production components
RUN cd rust_production && cargo build --release

# Stage 2: Runtime environment
FROM ubuntu:22.04 as runtime

# Install runtime dependencies
RUN apt-get update && apt-get install -y \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Install Elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
ENV PATH="/root/.elan/bin:$PATH"

# Install Lean 4.8.0
RUN elan toolchain install leanprover/lean4:v4.8.0
RUN elan default leanprover/lean4:v4.8.0

# Install Rust (minimal installation)
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable --profile minimal
ENV PATH="/root/.cargo/bin:$PATH"

# Set working directory
WORKDIR /app

# Copy built artifacts from builder stage
COPY --from=builder /app /app
COPY --from=builder /root/.elan /root/.elan
COPY --from=builder /root/.cargo /root/.cargo

# Create non-root user for security
RUN useradd -m -u 1000 endkan
RUN chown -R endkan:endkan /app
USER endkan

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD lake exe test || exit 1

# Default command
CMD ["lake", "exe", "test"]

# Metadata
LABEL org.opencontainers.image.title="EndKan"
LABEL org.opencontainers.image.description="Practical Automation for Ends, Coends, and Kan Extensions in Lean 4"
LABEL org.opencontainers.image.version="0.1.0"
LABEL org.opencontainers.image.authors="EndKan Team"
LABEL org.opencontainers.image.licenses="Apache-2.0"
LABEL org.opencontainers.image.source="https://github.com/fraware/lean-endkan"
LABEL org.opencontainers.image.documentation="https://github.com/fraware/lean-endkan/blob/main/README.md"

# Expose ports (if needed for web services)
EXPOSE 8080

# Volume for persistent data
VOLUME ["/app/data"]
