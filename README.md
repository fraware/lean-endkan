<div align="center">

# EndKan

**Ends, coends, and Kan extensions in Lean&nbsp;4**

[![CI](https://github.com/fraware/lean-endkan/actions/workflows/ci.yml/badge.svg)](https://github.com/fraware/lean-endkan/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Lean 4](https://img.shields.io/badge/Lean%204-4.8.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.8.0-green.svg)](https://github.com/leanprover-community/mathlib4)

*Tactics and definitions on [Mathlib](https://github.com/leanprover-community/mathlib4)*

</div>

---

> A small library for category-theoretic universal constructions: ends and coends, left and right Kan extensions, Beck–Chevalley machinery, and tactics that automate common proof steps.

---

## At a glance

| | |
| :--- | :--- |
| **Core** | Lean library (`EndKan`): types, lemmas, and registered tactics |
| **Toolchain** | Lean 4.8.0 and Mathlib `v4.8.0` (pinned in `Lakefile.lean` / `lean-toolchain`) |
| **Optional** | Rust CLI in `rust_production/` for health checks and demo benchmarks (not required to use the library) |

---

## What you get

- **Ends and coends** — definitions and β/η-style reasoning helpers  
- **Kan extensions** — left/right Kan, fusion-style steps where the theory applies  
- **Beck–Chevalley** — square infrastructure and dedicated tactics  
- **Configurable automation** — timeouts, tracing, and step limits via `endkan.*` options  

For a flat list of every tactic name, see [docs/TACTIC_INDEX.md](docs/TACTIC_INDEX.md).

---

## Quick start

Clone, fetch dependencies, build, and run the main Lean test executable:

```bash
git clone https://github.com/fraware/lean-endkan.git
cd lean-endkan
lake update
lake build
lake exe test
```

Other executables from `Lakefile.lean`: `lake exe run_tests`, `lake exe run_production_tests`, `lake exe deploy_production`, `lake exe test-runner`.

---

## Add EndKan to your project

In `Lakefile.lean`, depend on this repository and pin a branch or revision you trust:

```lean
require «lean-endkan» from git
  "https://github.com/fraware/lean-endkan.git" @ "main"
```

In your Lean files:

```lean
import EndKan
```

---

## Optional Rust CLI

From the repo root:

```bash
cd rust_production
cargo build --release
./target/release/endkan health
```

On Windows, the binary is typically `target\release\endkan.exe`.

Subcommands: `test`, `monitor`, `benchmark`, `health`, `report`. Use `endkan <subcommand> --help` for flags.

---

## Docker

Build and run the health check (image ships the Rust binary; it does not include a full Lean toolchain at runtime):

```bash
docker build -t endkan:local .
docker run --rm endkan:local health
```

---

## Documentation

| Resource | Contents |
| :--- | :--- |
| [docs/API.md](docs/API.md) | Public names, options, and tactic overview |
| [docs/TACTIC_INDEX.md](docs/TACTIC_INDEX.md) | Complete tactic list |
| [docs/TACTIC_SYSTEM.md](docs/TACTIC_SYSTEM.md) | How tactics compose and interact |
| [docs/BUILDING_DOCS.md](docs/BUILDING_DOCS.md) | Keeping documentation up to date |
| [docs/MATHLIB_UPGRADE.md](docs/MATHLIB_UPGRADE.md) | Lean / Mathlib version bumps |
| [tests/README.md](tests/README.md) | Test layout and runners |
| [DEPLOYMENT.md](DEPLOYMENT.md) | Builds, containers, and releases |
| [CONTRIBUTING.md](CONTRIBUTING.md) | How to contribute |
| [SECURITY.md](SECURITY.md) | Reporting security issues |

---

## License and links

Licensed under **Apache 2.0** — see [LICENSE](LICENSE).

[Open an issue](https://github.com/fraware/lean-endkan/issues) · [Browse `docs/`](docs/)
