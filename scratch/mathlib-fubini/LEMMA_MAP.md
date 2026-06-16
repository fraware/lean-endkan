# Fubini — Mathlib upstream lemma map

Staging for the **third** Mathlib extraction wave (see `docs/EXTRACTION_LEDGER.md` §5–§6).
Source: `EndKan.Fubini.*`. Target Mathlib pin: `v4.31.0-rc1`.

## Mathlib overlap

Mathlib has `Limits.end_` / `Limits.coend` on curried profunctors but **no packaged
nested product Fubini** swapping an end over `C × D` with ends over `C` at fixed `d`.

## Status key

- **ready** — kernel-checked, plausible Mathlib naming
- **hypothesis** — needs explicit typeclass (extraction boundary on rc1)
- **defer** — design issue or automation-only

## End Fubini

| Status | EndKan name | Local path | Proposed Mathlib path |
|--------|-------------|------------|----------------------|
| ready | `endSliceEmbed`, `endSlice` | `Fubini/Slice.lean` | `.../Ends/Fubini/Slice.lean` |
| ready | `endInnerObj`, `endInnerπ`, `endInnerLift` | Slice | Fubini/Slice |
| ready | `endInnerMap`, `endInnerMap_spec` | Slice | Fubini/Slice |
| ready | `endSlice_cov_contr` | Slice | Fubini/Slice |
| hypothesis | `AllEndSliceContrIso`, `endSliceOpCovIso` | Slice | documented boundary |
| ready | `endOuterProfunctor` | `Fubini/Nested.lean` | `.../Ends/Fubini/Nested.lean` |
| ready | `endFubiniIso`, `endFubiniIso_hom` | Nested | Fubini/Nested |
| ready | `end_fubini_target` | `Fubini.lean` | Fubini API |
| ready | `end_fubini_beta`, `end_fubini_π` | Fubini.lean | thin re-exports |
| defer | `EndSliceJointMono` bootstrap | Slice | rc1 mutual `IsIso` blocked |

## Coend Fubini

| Status | EndKan name | Local path | Proposed Mathlib path |
|--------|-------------|------------|----------------------|
| ready | `coendSliceEmbed`, `coendSlice` | `Fubini/CoendSlice.lean` | `.../Coends/Fubini/Slice.lean` |
| ready | `coendInnerMap`, `coendInnerDesc` | CoendSlice | Fubini/Slice |
| ready | `coendSliceMid_*` | CoendSlice | mid-level API (not `ι ≫ Cov`) |
| hypothesis | `CoendSliceContrIso` | CoendSlice | documented boundary |
| ready | `coendFubiniIso` | `Fubini/NestedCoend.lean` | Fubini/Nested |
| ready | `coend_fubini_target` | Fubini.lean | Fubini API |

## Consumer example (not for Mathlib PR body)

`EndKan.Fubini.Examples` — constant profunctor on `OneCat` discharges hypothesis
classes via `allEndSliceContrIsoOfData` / `coendSliceContrIsoOfData`.
