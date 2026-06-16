# Mathlib PR: diagonal end β/η lemmas

## PR title

`feat(CategoryTheory/Limits): diagonal end β/η lemmas for profunctors on Cᵒᵖ × C`

## Summary

Mathlib already defines ends for `F : Jᵒᵖ ⥤ J ⥤ C` (`Limits.end_`, wedges, `end_.lift_π`,
`end_.condition`, functoriality). This PR adds a **diagonal profunctor layer** for functors
`F : Cᵒᵖ × C ⥤ D` (curried as `endBifunctor F`) together with named **β/η rewrite lemmas**
and abstract examples. The mathematical content is extracted from
[`lean-endkan`](https://github.com/mateo/lean-endkan) `EndKan.End.Core` and `EndKan.End.BetaEta`.

Staging artifacts live in `scratch/mathlib-end-beta/` (`LEMMA_MAP.md`, `MODULE_STRUCTURE.md`,
`src/Scratch/MathlibEndBetaExamples.lean`).

## Motivation

Users of profunctor ends on `Cᵒᵖ × C` currently thread `curry.obj F` and diagonal wedge
data by hand. Named `beta` / `eta` lemmas (analogous to λ-calculus reduction) make proofs
through `end_.π` and `end_.lift` predictable without local tactic infrastructure.

## Proposed files

| Mathlib path | Content |
|--------------|---------|
| `CategoryTheory/Limits/Shapes/End/Diagonal.lean` | `endBifunctor`, diagonal wedge data, `endDiagonal`, `post_ext` |
| `CategoryTheory/Limits/Shapes/End/BetaEta.lean` | `beta`, `eta`, `π_beta` |
| `CategoryTheory/Limits/Shapes/End/Examples.lean` | Abstract usage theorems (no tactics) |

Existing `CategoryTheory/Limits/Shapes/End.lean` stays unchanged in PR #1.

## Lemma checklist

### New declarations (intended)

- [ ] `Limits.endBifunctor` + `@[simp]` fiber lemmas (`obj_map`, `map_app`, `obj_obj`, `fiber_obj`)
- [ ] `Limits.post_comp_endBifunctor_map`
- [ ] `DiagonalWedge` (or documented equivalence with `Wedge (endBifunctor F)`)
- [ ] `endDiagonal`, `endDiagonal.π`, `endDiagonal.lift`, `endDiagonal.lift_π`
- [ ] `endDiagonal.hom_ext` (alias of `end_.hom_ext`)
- [ ] `endDiagonal.post_ext`, `endDiagonal.post_uniq`
- [ ] `endDiagonal.map`, `endDiagonal.map_π`
- [ ] `endDiagonal.beta`, `endDiagonal.eta`, `endDiagonal.π_beta`
- [ ] Examples: `diagonal_beta`, `diagonal_eta`, `diagonal_map_π`, `diagonal_post_ext`

### Explicitly omitted (already in Mathlib or trivial)

- [ ] `end_.map_id`, `end_.map_comp` — use existing `end_.map_id` / `end_.map_comp`
- [ ] `end_π_eta` — reflexivity only
- [ ] EndKan tactics, attributes, telemetry

## Test plan

- [ ] `lake build` on Mathlib CI (new modules only; no import-graph regressions)
- [ ] `#guard_msgs` / `example` blocks in `Examples.lean` elaborate cleanly
- [ ] `simp` set: fiber lemmas and `π_beta` reduce profunctor compositions as expected
- [ ] Downstream: none required; optional follow-up to use `endDiagonal.beta` in category theory libs

## Local verification (lean-endkan)

```powershell
lake build EndKan
lake build Scratch.MathlibEndBetaExamples
.\scripts\acceptance.ps1
```

## Dependency notes

- **Lean / Mathlib pin:** `v4.31.0-rc1` (matches current `lean-endkan` `lakefile.lean`)
- **Imports:** only `Limits.Shapes.End`, `Functor.Currying`, `Products.Basic`, `Opposites`
- **No new typeclass axioms**; all lemmas assume `[HasEnd (endBifunctor F)]`
- **Review risk:** naming `DiagonalWedge` vs reusing `Wedge`; whether `endDiagonal` deserves
  a separate namespace vs top-level abbreviations. Cowedge dual API deferred unless requested.

## Remaining gaps before Mathlib submission

1. **Maintainer naming pass** on `endDiagonal` / `DiagonalWedge` / `beta` vs `end_beta`
2. **Physical module layout** — new `End/` directory vs extending monolithic `End.lean`
3. **simp-normal form** coordination with existing `end_.lift_π` and `curry` simp lemmas
4. **Port proofs** from `src/Scratch/MathlibEndBetaExamples.lean` into Mathlib namespace
   (replace `EndKan.End` imports)
5. **CHANGELOG** entry and docs module link on Mathlib website
6. **No Zulip / Mathlib issue yet** — open a short design thread before the PR if reviewers
   prefer wedge-only API without `DiagonalWedge`

## Related

- `docs/EXTRACTION_LEDGER.md` §1 (first upstream PR in sequence)
- Next extraction: coend β/η (`EndKan.Coend.*`)
