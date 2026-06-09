# Modernization and extraction sprint

This document records the first modernization and extraction plan for `lean-endkan` as part of the broader category-theory contribution program targeting Mathlib and CSLib.

## Current repository position

`lean-endkan` is the most directly Mathlib-facing repository in the portfolio. It targets ends, coends, Fubini-style constructions, left and right Kan extensions, Beck-Chevalley infrastructure, and tactics.

The repository has strong upstream potential, but the public import currently combines core mathematics with tactics, attributes, telemetry, optimization, configuration, monitoring, and regression modules. That is too broad for upstream extraction.

Current constraints:

- Current toolchain in `lean-toolchain`: `leanprover/lean4:v4.8.0`.
- `Lakefile.lean` pins Mathlib at `v4.8.0`.
- The README identifies the core mathematical targets as ends, coends, Kan extensions, Beck-Chevalley machinery, and configurable automation.
- The top-level import includes both core mathematical files and demo or operational modules.

## Sprint objective

The objective is to port the mathematical core to the Lean 4.31 / current-Mathlib line and extract a small sequence of Mathlib PR candidates around ends, coends, Kan extensions, and Beck-Chevalley reasoning.

The first upstream outputs should be definitions, beta/eta lemmas, API lemmas, and examples. Tactics should remain local until the mathematical surface is accepted and stable.

## Modernization gates

### Gate 1: port to current Mathlib

Update the Lean and Mathlib pins to the current Mathlib baseline and build the core modules first.

Required commands:

```bash
lake update
lake build EndKan
lake exe test
lake exe run_tests
lake exe test-runner
```

Expected first failures to check:

- moved Mathlib imports for ends, coends, limits, functor categories, and natural transformations;
- changes to category-theory notation;
- changes to limits and colimits API;
- tactic elaboration drift for `end_beta`, `end_eta`, `coend_beta`, `coend_eta`, `kan_fuse`, and `beck_chevalley!`;
- imports that should move out of the stable public API.

### Gate 2: split core mathematics from automation

Recommended stable layout:

```text
EndKan/Core.lean                  -- stable public mathematical imports
EndKan/End/Core.lean
EndKan/End/BetaEta.lean
EndKan/Coend/Core.lean
EndKan/Coend/BetaEta.lean
EndKan/Fubini.lean
EndKan/Kan/Core.lean
EndKan/Kan/BeckChevalley.lean
EndKan/Automation.lean            -- tactics and attributes
EndKan/Experimental.lean          -- telemetry, monitoring, regression, optimization
EndKan.lean                       -- stable public import only
```

The stable top-level import should not import telemetry, monitoring, regression, or optimization modules.

### Gate 3: upstream extraction ledger

For each mathematical module, record exactly which statements are absent or awkward in current Mathlib.

Required ledger columns:

- construction;
- current local name;
- current Mathlib overlap;
- proposed Mathlib file path;
- theorem or definition statement;
- proof dependencies;
- review risk;
- downstream examples unlocked.

## Extraction targets

### Target A: ends and coends

First candidate area:

- beta-style projection/injection lemmas;
- eta-style uniqueness lemmas;
- simp-normal forms for common end and coend proofs;
- small examples showing current Mathlib usage.

These should be the first Mathlib PRs because they are local, reviewable, and valuable for users.

### Target B: Fubini-style lemmas

Second candidate area:

- end/coend Fubini statements;
- naturality and reassociation lemmas needed for proofs;
- examples that do not require the tactic layer.

These should only be proposed after the beta/eta surface is stable.

### Target C: Kan extensions

Third candidate area:

- left and right Kan extension helper lemmas;
- naturality lemmas for Kan extension constructions;
- small examples that avoid broad automation.

### Target D: Beck-Chevalley infrastructure

Beck-Chevalley material should be staged carefully. The first contribution should be a design discussion or a minimal square abstraction, unless current Mathlib already has a natural target file.

## Non-upstream material for now

The following should remain repository-local during this sprint:

- `endkan_smart`;
- debug tactic variants;
- telemetry;
- optimization;
- monitoring;
- regression infrastructure;
- Rust CLI and Docker material;
- production benchmark modules.

## First PR candidates generated from this repo

1. Local modernization PR: port core mathematical modules to Lean 4.31 and current Mathlib.
2. Local architecture PR: split stable mathematical import from automation and experimental modules.
3. Local audit PR: create an extraction ledger for ends, coends, Fubini, Kan, and Beck-Chevalley material.
4. Mathlib candidate PR: beta/eta lemmas and examples for ends.
5. Mathlib candidate PR: beta/eta lemmas and examples for coends.
6. Mathlib candidate PR: carefully scoped Fubini helper lemmas.
7. Mathlib candidate PR: minimal Kan extension helper lemmas.

## Build certification status

This document is a planning and extraction artifact. It does not certify that the repository has been built on Lean 4.31 yet. Certification requires a successful local or CI run of the commands in Gate 1.
