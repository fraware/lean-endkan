# Mathlib extraction ledger

This document tracks EndKan lemmas that are candidates for upstream Mathlib PRs on
Lean `v4.31.0-rc1` / Mathlib `v4.31.0-rc1`. As of 2026-06-15, `leanprover/lean4:v4.31.0`
stable is not released (latest stable: `v4.30.0`; latest prerelease: `v4.31.0-rc1`), so
the iso-bootstrap mutual-instance experiment stays on rc1. Repository-local automation and
experimental modules are out of scope.

## Upstream order

Planned Mathlib PR sequence (this repository is **extraction staging** — not ready for the
deepest Mathlib stream yet; automation and experimental modules stay local).

1. **First PR:** `CategoryTheory` end β/η examples and helper lemmas (`EndKan.End.Core`,
   `EndKan.End.BetaEta`)
2. **Second PR:** coend β/η examples and helper lemmas (`EndKan.Coend.Core`,
   `EndKan.Coend.BetaEta`)
3. **Later:** Fubini helper lemmas (ends and coends), Kan extension helpers, Beck–Chevalley
   design issue (`EndKan.Fubini`, `EndKan.Kan.Core`, `EndKan.Kan.BeckChevalley`)

Optional geometric hypothesis instances live in `EndKan.Kan.BeckChevalley.Hypotheses` and are
not part of the default `EndKan` import boundary.

---

## 5. Fubini ends

| Item | Local name | Status | Notes |
|------|------------|--------|-------|
| Slice embedding | `endSliceEmbed`, `endSlice` | Proved | `Cᵒᵖ × C` into `EndIdx C D` at fixed `d` |
| Inner end | `endInnerObj`, `endInnerπ`, `endInnerLift` | Proved | `endInnerLift_π`, `endInnerLift_πWedge` |
| `d`-action on inner ends | `endInnerMap` | Proved | Characterized by `endInnerLift d ≫ endInnerMap f = endInnerLift d'` |
| Bootstrap iso | `endSliceOpCovIso`, `[AllEndSliceContrIso F]` | Hypothesis class + packager | Unconditional mutual bootstrap blocked on rc1 (Attempt 4: lemma stack + `allEndSliceContrIsoOfData` green; seeded `mutual def` fails WF recursion — see `Slice.lean` `sliceIsoBootstrap`). Joint-mono closure blocked (Attempt 5: cov iso + `EndSliceJointMono` insufficient — see `sliceIsoBootstrap` comment). Concrete consumer: `EndKan.Fubini.Examples` (`allEndSliceContrIsoOfData` on constant profunctor) |
| Nested outer end | `endOuterProfunctor`, `endNestedObj` | Proved | Functorial via `endInnerMap_id` / `comp` |
| Fubini iso | `endFubiniIso` | Proved | `EndObj F ≅ endNestedObj F`; `@[simp] endFubiniIso_hom` |
| Indexing | `EndIdx C D` | Defeq | `(C × D)ᵒᵖ × (C × D)`; `endWedge_eq_op` |

**Mathlib overlap:** Mathlib has `Limits.end_` for profunctors; no packaged nested
product Fubini. Proposed path: `Mathlib/CategoryTheory/Limits/Shapes/Ends/Fubini.lean`
(scoped helper lemmas first).

**Proof dependencies:** `EndKan.End.Core`, `EndKan.Fubini.Slice`, `EndKan.Fubini.Nested`.

---

## 6. Fubini coends

| Item | Local name | Status | Notes |
|------|------------|--------|-------|
| Slice embedding | `coendSliceEmbed`, `coendSlice` | Proved | `C × Cᵒᵖ` into `(C × D) × (C × D)ᵒᵖ` |
| Inner coend | `coendInnerObj`, `coendInnerι`, `coendInnerDesc` | Proved | `coendInnerDesc d = coendInnerMap f ≫ coendInnerDesc d'` |
| `d`-action | `coendInnerMap` | Proved | Cov-only path via `coendSliceCov`; no global bootstrap iso |
| Hypothesis class | `[CoendSliceContrIso F]` | Hypothesis + packager | Contr iso + mid epi per leg; mirror lemma stack in `CoendSlice.lean` (`coendSliceContrIsoOfData`). Joint-mono closure blocked (Attempt 5). Concrete consumer: `EndKan.Fubini.Examples` (`coendSliceContrIsoOfData` on constant profunctor) |
| Nested outer coend | `coendOuterProfunctor`, `coendNestedObj` | Proved | Mirror of end side |
| Fubini iso | `coendFubiniIso` | Proved | `CoendObj F ≅ coendNestedObj F`; `@[simp] coendFubiniIso_hom` |

**Mathlib overlap:** `Limits.coend` diagonal API; nested product Fubini absent.
Proposed path: parallel to end Fubini helpers in Mathlib.

**Proof dependencies:** `EndKan.Coend.Core`, `EndKan.Fubini.CoendSlice`, `EndKan.Fubini.NestedCoend`.

---

## 10. Beck–Chevalley

| Item | Local name | Mathlib-ready? | Notes |
|------|------------|----------------|-------|
| Square | `Square`, `reflSquare` | API | Commutative square `K ⋙ M = L ⋙ N` |
| Comparison | `beckChevalleyCompare` | Yes | Pointwise left Kan extension comparison |
| Hypothesis bundle | `BeckChevalley`, `PullbackSquare`, `FullyFaithfulSquare`, `ExactSquare` | Partial | `compare_iso` field records isomorphism |
| Reflexive instance | `reflSquare_beckChevalley` | **Proved** | From `[IsEquivalence K]` via `Hypotheses.lean` |
| Pullback instance | `pullbackSquare_of_equivalence` | **Proved** | Equivalence on vertical leg; full comma pullback deferred |
| Fully faithful | `fullyFaithfulSquare_of_equivalence` | **Proved** | Under `[IsEquivalence K,L]` + `[Faithful M]` |
| Exact / PES | `exactSquare_of_equivalence` | **Proved** | `[Faithful L]`, `[PreservesFilteredColimits M]` |
| Tactic extraction | `beckChevalleyIso`, `beckChevalleyPullback` | Yes | `beck_chevalley!` on registered squares |
| Comma pullback | `IsPullbackSquare.comma_pullback` | Boundary | `beckChevalleySouth`/`North` aliases + `square_comm_whisker` + `refl_beckChevalleySouth_eq` in `Hypotheses.lean`; Mathlib `Comma.final_fst` hook deferred (exe link bloat) |

**Automation keys:** `beckChevalleyIso`, `beckChevalleyPullback`, `beckChevalleyFullyFaithful`
in `Transformation.lean` / `Optimization.lean` / `Tactics.lean`.

**Review risk:** Pullback Beck–Chevalley from comma-category finality remains the main
upstream gap; current proofs use equivalence hypotheses acceptable for extraction staging.
