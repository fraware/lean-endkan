# Mathlib PR: diagonal coend β/η lemmas

## PR title

`feat(CategoryTheory/Limits): diagonal coend β/η lemmas for profunctors on C × Cᵒᵖ`

## Summary

Mathlib already defines coends for `F : Cᵒᵖ ⥤ C ⥤ E` (`Limits.coend`, dinaturality, `coend.ι_desc`,
`coend.condition`, functoriality). This PR adds a **diagonal profunctor layer** for functors
`F : C × Cᵒᵖ ⥤ E` (swap + currying as `coendBifunctor F`) together with named **β/η rewrite lemmas**
and abstract examples. The mathematical content is extracted from
[`lean-endkan`](https://github.com/fraware/lean-endkan) `EndKan.Coend.Core` and `EndKan.Coend.BetaEta`.

Staging artifacts live in `scratch/mathlib-coend-beta/` (`LEMMA_MAP.md`, `MODULE_STRUCTURE.md`,
`src/Scratch/MathlibCoendBetaExamples.lean`).

## Motivation

Users of profunctor coends on `C × Cᵒᵖ` currently thread `Prod.swap`, `curry.obj`, and diagonal
dinaturality data by hand. Named `beta` / `eta` lemmas (analogous to λ-calculus reduction) make proofs
through `coend.ι` and `coend.desc` predictable without local tactic infrastructure.

## Proposed files

| Mathlib path | Content |
|--------------|---------|
| `CategoryTheory/Limits/Shapes/Coend/Diagonal.lean` | `coendSwap`, `coendBifunctor`, diagonal dinaturality, `coendDiagonal`, `eqToHom` bridge |
| `CategoryTheory/Limits/Shapes/Coend/BetaEta.lean` | `beta`, `eta`, `ι_beta` |
| `CategoryTheory/Limits/Shapes/Coend/Examples.lean` | Abstract usage theorems (no tactics) |

Existing coend API in Mathlib stays unchanged in PR #2.

## Lemma checklist

### New declarations (intended)

- [ ] `coendSwap`, `coendBifunctor` + `@[simp]` fiber lemmas (`coendDiagonal`, `map_app`, `obj_map`)
- [ ] `coendNatTrans`
- [ ] `DiagonalDinaturality` (or documented equivalence with curried dinaturality)
- [ ] `DiagonalDinaturality.ofDiagonal`
- [ ] `eqToHom_symm_comp_mpr_diagonal`, `mpr_hom_ιCurry`
- [ ] `coendDiagonal`, `coendDiagonal.ιCurry`, `coendDiagonal.ι`, `coendDiagonal.desc`
- [ ] `coendDiagonal.ι_desc`, `coendDiagonal.hom_ext` (alias of `coend.hom_ext`)
- [ ] `coendDiagonal.map`, `coendDiagonal.map_ιCurry`
- [ ] `coendDiagonal.beta`, `coendDiagonal.eta`, `coendDiagonal.ι_beta`
- [ ] Examples: `diagonal_beta`, `diagonal_eta`, `diagonal_ι_dinatural`, `diagonal_map_ιCurry`

### Explicitly omitted (already in Mathlib or trivial)

- [ ] `coend.map_id` — use existing `coend.map_id`
- [ ] `coend_ι_eta` — reflexivity only
- [ ] `coend_ιCurry_beta` — alias of `coend.condition`
- [ ] EndKan tactics, attributes, telemetry

## Test plan

- [ ] `lake build` on Mathlib CI (new modules only; no import-graph regressions)
- [ ] `#guard_msgs` / `example` blocks in `Examples.lean` elaborate cleanly
- [ ] `simp` set: fiber lemmas and `ι_beta` reduce profunctor compositions as expected
- [ ] Downstream: none required; optional follow-up to use `coendDiagonal.beta` in category theory libs

## Local verification (lean-endkan)

```powershell
lake build EndKan
lake build Scratch.MathlibCoendBetaExamples
.\scripts\acceptance.ps1
```

## Dependency notes

- **Lean / Mathlib pin:** `v4.31.0` (matches current `lean-endkan` `lakefile.lean`)
- **Imports:** coend API, `Functor.Currying`, `Products.Basic`, `Whiskering`, `EqToHom`
- **No new typeclass axioms**; all lemmas assume `[HasCoend (coendBifunctor F)]`
- **Review risk:** naming `DiagonalDinaturality` vs reusing existing dinaturality structures;
  whether `coendDiagonal` deserves a separate namespace vs top-level abbreviations.

## Remaining gaps before Mathlib submission

1. **Maintainer naming pass** on `coendDiagonal` / `DiagonalDinaturality` / `beta` vs `coend_beta`
2. **Physical module layout** — new `Coend/` directory vs extending existing coend modules
3. **simp-normal form** coordination with existing `coend.ι_desc` and `curry` simp lemmas
4. **Port proofs** from `src/Scratch/MathlibCoendBetaExamples.lean` into Mathlib namespace
   (replace `EndKan.Coend` imports)
5. **CHANGELOG** entry and docs module link on Mathlib website
6. **Coordinate with PR #1** (end β/η) for symmetric API naming (`endDiagonal` / `coendDiagonal`)

## Related

- `docs/EXTRACTION_LEDGER.md` §2 (second upstream PR in sequence)
- Prior extraction: end β/η (`EndKan.End.*`, `docs/MATHLIB_PR_END_BETA_ETA.md`)
