# Mathlib PR: nested Fubini for ends and coends

## PR title

`feat(CategoryTheory/Limits): nested product Fubini helpers for ends and coends`

## Summary

Package **nested Fubini** isomorphisms for profunctors on product categories:

- `EndObj F ≅ endNestedObj F` for `F : (C × D)ᵒᵖ × (C × D) ⥤ E`
- `CoendObj F ≅ coendNestedObj F` for `F : (C × D) × (C × D)ᵒᵖ ⥤ E`

Extracted from `EndKan.Fubini` (`Slice`, `Nested`, `CoendSlice`, `NestedCoend`).
Staging: `scratch/mathlib-fubini/`, `src/Scratch/MathlibFubiniExamples.lean`.

## Motivation

Mathlib users currently hand-assemble slice embeddings, inner ends/coends, and nested
outer profunctors. A small Fubini library reduces bookkeeping for double limits over
`C × D`.

## Proposed files (phased)

| Phase | Mathlib path | Content |
|-------|--------------|---------|
| 1 | `Limits/Shapes/End/Fubini/Slice.lean` | `endSlice`, `endInnerMap`, wedge lemmas |
| 2 | `Limits/Shapes/End/Fubini/Nested.lean` | `endFubiniIso` under hypothesis class |
| 3 | `Limits/Shapes/Coend/Fubini/*` | coend mirror |
| 4 | `Limits/Shapes/*/Fubini/Examples.lean` | constant functor instance |

## Lemma checklist

### Ready for Mathlib (with hypothesis)

- [ ] `endSliceEmbed`, `endSlice`, `endWedge`, indexing `@[simp]` lemmas
- [ ] `endInnerObj`, `endInnerπ`, `endInnerLift`, `endInnerMap` + spec/id/comp
- [ ] `endSlice_cov_contr` (from `Limits.end_.condition`)
- [ ] `endOuterProfunctor`, `endNestedObj`, `endFubiniForward` / `Backward`, `endFubiniIso`
- [ ] Coend mirror: `coendSlice*`, `coendInnerMap`, `coendFubiniIso`
- [ ] Public targets `end_fubini_target`, `coend_fubini_target`

### Documented boundary (not hidden)

- [ ] `AllEndSliceContrIso` / `CoendSliceContrIso` — contr-leg iso per profunctor
- [ ] rc1 mutual `IsIso` bootstrap failure (see `scratch/SliceIsoMin.lean`)

### Explicitly deferred

- [ ] Unconditional contr-leg iso instances
- [ ] EndKan tactics, telemetry, FFI
- [ ] Full comma-category Beck–Chevalley (separate design issue)

## Test plan

- [ ] `lake build` Mathlib CI on new modules
- [ ] Constant profunctor example (`OneCat`) elaborates `endFubiniIso`
- [ ] No import of automation / experimental modules

## Local verification

```powershell
lake build EndKan.Fubini
lake build Scratch.MathlibFubiniExamples
.\scripts\acceptance.ps1
```

## Remaining gaps before Mathlib submission

1. Maintainer agreement on hypothesis class vs cov-only inner map
2. Naming: `EndIdx` vs raw `Prod ((C×D)ᵒᵖ) (C×D)`
3. Whether Fubini PR waits for end/coend β/η PRs (#1–#2) to land first
4. Zulip design thread before opening Mathlib PR
