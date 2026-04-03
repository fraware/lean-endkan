# EndKan test suite (Lean)

Test modules and the test runner live under **`src/EndKan/`** (for example `UnitTests/`, `IntegrationTests/`, `TestRunner.lean`). They build together with the library when you run `lake build` at the repository root.

## Running tests

From the repo root:

```bash
lake update
lake build

# Short smoke tests
lake exe test
lake exe run_tests

# Framework runner (config name, then test kinds)
lake exe test-runner -- dev unit
lake exe test-runner -- ci unit integration e2e performance
```

Optional executables that exercise benchmark and monitoring demos:

```bash
lake exe run_production_tests
lake exe deploy_production
```

## Rust tests

```bash
cd rust_production && cargo test
```

## About this folder

`tests/` holds documentation only. The real test sources are under `src/EndKan/` in the main project.
