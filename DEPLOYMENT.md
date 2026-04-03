# Running EndKan outside a dev checkout

## Lean library

Most people only need the library:

```bash
git clone https://github.com/fraware/lean-endkan.git
cd lean-endkan
lake update
lake build
```

Add the project as a dependency from your own `Lakefile.lean` (see [README.md](README.md)).

## Rust program

The `endkan` binary is built from the `rust_production` folder:

```bash
cd rust_production
cargo build --release
./target/release/endkan health
```

Subcommands: `test`, `monitor`, `benchmark`, `health`, `report`. Use `--help` on the binary or on a subcommand.

Installing from the internet package registry only works if the crate is published there; otherwise build from a clone of this repository.

## Docker

Build and run locally:

```bash
docker build -t endkan:local .
docker run --rm endkan:local health
```

The default command runs `health`. The runtime image contains the `endkan` binary only (Lean is used in the build stage, not shipped in the final image).

If you use [docker-compose.yml](docker-compose.yml), follow the comments in that file for your setup.

## Automated checks

When you push changes, the repository’s GitHub workflows build the Lean project and the Rust program, run tests, and scan Rust dependencies. Creating a **git tag** matching `v*.*.*` triggers a release workflow that attaches a Linux binary to the GitHub release.

## Environment variables (Rust)

You can turn up logging while debugging the Rust tool, for example:

```bash
export RUST_LOG=info
```

## Health and checks

- From Docker or a local Rust build: `endkan health`.  
- From a full Lean checkout: `lake exe test` (see [tests/README.md](tests/README.md)).

## Security notes for containers

Run as a non-root user when your platform allows it, set memory and CPU limits for untrusted workloads, and avoid putting secrets in image layers. See [SECURITY.md](SECURITY.md) for reporting vulnerabilities.
