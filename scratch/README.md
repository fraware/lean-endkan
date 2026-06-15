# Scratch regression harness

This directory holds **isolated** Lean files used to validate proof patterns before
porting them into `src/EndKan/Fubini/`. The Lake CI target is `Scratch.SliceIsoMin`
(`src/Scratch/SliceIsoMin.lean`); local experiments stay under `scratch/`.

## Kept reference files

| File | Purpose |
|------|---------|
| `SliceIsoMin.lean` | Mutual `IsIso.mk` bootstrap experiment for `endSliceContr` / `endSliceCov` |
| `IsoCheck.lean` | Documents `IsIso` / `Iso.mk` field order on Lean 4.31-rc1 |

## Compile locally

```powershell
lake build Scratch.SliceIsoMin
lake build EndKan.Fubini.Slice EndKan.Fubini.CoendSlice
lake env lean scratch/SliceIsoMin.lean
```

The `scratch/` tree imports `EndKan`; run after `lake build EndKan`.

## Production mapping

- `SliceIsoMin` iso lemmas → `src/EndKan/Fubini/Slice.lean`
  - Unconditional: `endSliceOpCovIso_isIso`, `endSliceCov_hom_inv`, `endSliceCov_inv_hom`
  - Packaging: `endSliceContrIsoFromData`, `allEndSliceContrIsoOfData`
  - Hypothesis: `[AllEndSliceContrIso F]` (rc1 blocks unconditional mutual bootstrap; see `sliceIsoBootstrap` comment)
- Coend mirror → `src/EndKan/Fubini/CoendSlice.lean` (`coendSliceContrIsoFromData`, `coendSliceContrIsoOfData`)
- Nested Fubini proofs → `src/EndKan/Fubini/Nested.lean` / `NestedCoend.lean`

## rc1 bootstrap status (Attempt 4–5)

Seeded `mutual noncomputable def` / `mutual instance` on `endSliceContrIsoFromData` /
`endSliceCovIsoFromData` fails on Lean 4.31-rc1 (`synthInstanceFailed` circularity;
`mutual instance` retested on rc1 (2026-06; circular `synthInstanceFailed`). The lemma stack
and bilateral-data packagers are green in production; `[AllEndSliceContrIso F]` /
`[CoendSliceContrIso F]` remain the Fubini interface until stable v4.31.0 or a cov-only proof.

Acceptance gate: `scripts/acceptance.ps1` (build + scratch iso + exe tests).

## Removed

Obsolete one-off files (`eqtest*.lean`, deleted bootstrap copies) should not be reintroduced without updating this README.
