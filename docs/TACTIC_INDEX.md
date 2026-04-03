# Tactic list

These tactics are defined in [`src/EndKan/Tactics.lean`](../src/EndKan/Tactics.lean). Use this list when updating [TACTIC_SYSTEM.md](TACTIC_SYSTEM.md) or the root [README](../README.md).

## Core

- `end_beta`, `end_eta`
- `coend_beta`, `coend_eta`
- `kan_fuse`
- `beck_chevalley!`

## Variants with extra error reporting

- `end_beta!`, `end_eta!`
- `coend_beta!`, `coend_eta!`
- `kan_fuse!`
- `beck_chevalley!!`

## Combined and helper tactics

- `endkan_beta`, `endkan_eta`, `endkan_all`
- `endkan_smart`, `endkan_debug`

## `by` syntax

Where `Tactics.lean` defines a `by …` form, you can write proofs using that shorthand.
