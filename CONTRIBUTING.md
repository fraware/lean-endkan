# Contributing to EndKan

## Prerequisites

- [Elan](https://github.com/leanprover/elan) and Lean 4 (see [`lean-toolchain`](lean-toolchain); currently v4.8.0).
- [Rust](https://rustup.rs/) (stable) if you work on the optional Rust program in `rust_production/`.

## Clone and build (Lean)

```bash
git clone https://github.com/fraware/lean-endkan.git
cd lean-endkan
lake update
lake build
```

The first `lake update` downloads the Mathlib version fixed in [`Lakefile.lean`](Lakefile.lean). If you change that version, run `lake update` again and commit the updated dependency lock file (`lake-manifest.json`) together with your change.

## Run tests

```bash
lake exe test              # short smoke tests
lake exe run_tests         # longer smoke suite
lake exe test-runner -- dev unit
lake exe test-runner -- ci unit integration e2e performance
```

Rust program (`rust_production/`):

```bash
cd rust_production
cargo fmt
cargo clippy -- -D warnings
cargo test
```

## Before you open a change

- `lake build` works from the repository root.
- If you change public tactics or names, update [`docs/API.md`](docs/API.md) or [`docs/TACTIC_SYSTEM.md`](docs/TACTIC_SYSTEM.md) (see [`docs/BUILDING_DOCS.md`](docs/BUILDING_DOCS.md)).
- Small commits with clear messages are easier to review.

## Updating Mathlib

See [`docs/MATHLIB_UPGRADE.md`](docs/MATHLIB_UPGRADE.md).
