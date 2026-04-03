# Multi-stage Dockerfile: build Lean library + Rust CLI; run minimal image with CLI only.
FROM ubuntu:22.04 AS builder

RUN apt-get update && apt-get install -y \
    curl \
    build-essential \
    git \
    && rm -rf /var/lib/apt/lists/*

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
ENV PATH="/root/.elan/bin:$PATH"

RUN elan toolchain install leanprover/lean4:v4.8.0
RUN elan default leanprover/lean4:v4.8.0

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:$PATH"

WORKDIR /app
COPY . .

RUN lake update && lake build
RUN cd rust_production && cargo build --release

# Runtime: only the statically linked-ish CLI (dynamic libc only).
FROM ubuntu:22.04 AS runtime

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/rust_production/target/release/endkan /usr/local/bin/endkan

RUN useradd -m -u 1000 endkan
USER endkan
WORKDIR /home/endkan

ENTRYPOINT ["/usr/local/bin/endkan"]

HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD /usr/local/bin/endkan health || exit 1

CMD ["health"]

LABEL org.opencontainers.image.title="EndKan"
LABEL org.opencontainers.image.description="EndKan Rust CLI (Lean library is built in the builder stage)"
LABEL org.opencontainers.image.version="0.1.0"
LABEL org.opencontainers.image.licenses="Apache-2.0"
LABEL org.opencontainers.image.source="https://github.com/fraware/lean-endkan"

EXPOSE 8080
VOLUME ["/home/endkan/data"]
