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

## 1. End β/η (first PR)

| Item | Local name | Status | Notes |
|------|------------|--------|-------|
| Curried bifunctor | `endBifunctor` | Proved | `Cᵒᵖ × C ⥤ D` → `Cᵒᵖ ⥤ C ⥤ D`; `@[simp]` fiber lemmas |
| Dinaturality | `DinaturalTransformation`, `Cowedge` | Proved | Diagonal wedge data for `Limits.end_` |
| End object | `EndObj`, `π`, `lift`, `uniq` | Proved | Thin wrapper over `Limits.end_`; `lift_π`, `π_natural` |
| Post-composition | `post_ext`, `post_uniq` | Proved | Yoneda-style uniqueness for maps from the end |
| Functoriality | `map`, `map_π`, `map_id`, `map_comp` | Proved | Via `Limits.end_.map` |
| β-reduction | `end_beta`, `end_π_beta` | Proved | `lift ω ≫ π F c = ω.app c`; projection dinaturality |
| η-expansion | `end_eta`, `end_π_eta` | Proved | Uniqueness from `uniq` |

**Mathlib overlap:** `Limits.end_`, `end_.π`, `end_.lift` exist; EndKan packages the
diagonal profunctor API (`Cᵒᵖ × C`) with named β/η lemmas. Proposed path:
`Mathlib/CategoryTheory/Limits/Shapes/Ends/BetaEta.lean`.

**Proof dependencies:** `EndKan.End.Core`, `EndKan.End.BetaEta`.

**Staging package:** `scratch/mathlib-end-beta/` (`LEMMA_MAP.md`, `MODULE_STRUCTURE.md`);
buildable examples in `src/Scratch/MathlibEndBetaExamples.lean`; PR brief in
`docs/MATHLIB_PR_END_BETA_ETA.md`.

---

## 2. Coend β/η (second PR)

| Item | Local name | Status | Notes |
|------|------------|--------|-------|
| Swap + currying | `coendSwap`, `coendBifunctor` | Proved | `@[simp]` diagonal and fiber lemmas |
| Key rewrite | `eqToHom_symm_comp_mpr_diagonal` | Proved | Bridges `F(c, op c)` and curried hom-types |
| Dinaturality | `DinaturalTransformation`, `ofDiagonal` | Proved | Diagonal data packaging for `Limits.coend` |
| Coend object | `CoendObj`, `ι`, `ιCurry`, `desc`, `uniq` | Proved | `desc_ι`, `desc_ιCurry`, `ιCurry_natural` |
| Functoriality | `map`, `map_ιCurry`, `coend_map_id` | Proved | Via `Limits.coend.map` |
| β-reduction | `coend_beta`, `coend_ι_beta`, `coend_ιCurry_beta` | Proved | Universal morphism commutation |
| η-expansion | `coend_eta`, `coend_ι_eta` | Proved | Uniqueness from `uniq` |

**Mathlib overlap:** `Limits.coend` diagonal API exists; EndKan adds explicit `C × Cᵒᵖ`
packaging and β/η lemmas. Proposed path:
`Mathlib/CategoryTheory/Limits/Shapes/Coends/BetaEta.lean`.

**Proof dependencies:** `EndKan.Coend.Core`, `EndKan.Coend.BetaEta`.

**Staging package:** `scratch/mathlib-coend-beta/` (`LEMMA_MAP.md`, `MODULE_STRUCTURE.md`);
buildable examples in `src/Scratch/MathlibCoendBetaExamples.lean`; PR brief in
`docs/MATHLIB_PR_COEND_BETA_ETA.md`.

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

**Staging package:** `scratch/mathlib-fubini/` (`LEMMA_MAP.md`, `MODULE_STRUCTURE.md`);
buildable examples in `src/Scratch/MathlibFubiniExamples.lean`; PR brief in
`docs/MATHLIB_PR_FUBINI.md`.

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

**Staging package:** shared with §5 — `scratch/mathlib-fubini/`, `src/Scratch/MathlibFubiniExamples.lean`,
`docs/MATHLIB_PR_FUBINI.md`.

---

## 7. Kan extension helpers

| Item | Local name | Status | Notes |
|------|------------|--------|-------|
| Pointwise Lan/Ran | `Lan`, `Ran` | Proved | Abbreviations over Mathlib `pointwiseLeftKanExtension` / `pointwiseRightKanExtension` |
| Object formulas | `lan_obj_eq`, `ran_obj_eq` | Proved | Colimit / limit of structured arrows |
| Beck–Chevalley square | `Square`, `reflSquare` | Proved | Commutative square `K ⋙ M = L ⋙ N` |
| Comparison map | `beckChevalleyCompare`, `BeckChevalleyTarget` | Proved | `Lan K (L ⋙ N ⋙ F) ⟶ M ⋙ F` |
| Hypothesis bundles | `PullbackSquare`, `FullyFaithfulSquare`, `ExactSquare`, `BeckChevalley` | Partial | `compare_iso` field; instances in `Hypotheses.lean` |
| Extraction lemmas | `beckChevalleyIso`, `beckChevalleyPullback` | Proved | Automation-facing; tactics stay local |

**Mathlib overlap:** Pointwise Kan extensions are in Mathlib; Beck–Chevalley design is the
main upstream gap. Proposed path: `Mathlib/CategoryTheory/Functor/KanExtension/BeckChevalley.lean`
(design issue first).

**Proof dependencies:** `EndKan.Kan.Core`, `EndKan.Kan.BeckChevalley`,
`EndKan.Kan.BeckChevalley.Hypotheses` (optional).

**Staging package:** `scratch/mathlib-kan-bc/` (`LEMMA_MAP.md`); design brief in
`docs/MATHLIB_PR_KAN_BECKCHEVALLEY.md`; examples in `src/Scratch/MathlibKanBcExamples.lean`.

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
