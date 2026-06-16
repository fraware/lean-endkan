# End β/η — Mathlib upstream lemma map

Staging for the **first** Mathlib extraction PR (see `docs/EXTRACTION_LEDGER.md` §1).
Source: `EndKan.End.Core`, `EndKan.End.BetaEta`. Target Mathlib pin: `v4.31.0-rc1`.

## Mathlib overlap (already upstream)

These Mathlib lemmas make several EndKan wrappers **thin aliases**. Do not re-upstream
as new declarations; reference them in proofs and docstrings.

| Mathlib | Role |
|---------|------|
| `Limits.end_`, `Limits.end_.π`, `Limits.end_.lift` | End object and universal morphisms |
| `Limits.end_.lift_π`, `Limits.end_.condition`, `Limits.end_.hom_ext` | Wedge axioms and uniqueness |
| `Limits.end_.map`, `Limits.end_.map_π`, `Limits.end_.map_id`, `Limits.end_.map_comp` | Functoriality |

## Lemma checklist (proposed upstream)

Status key: **ready** = minimal deps, no sorry, Mathlib naming plausible; **alias** = definitional
wrapper only; **review** = naming or API overlap needs Mathlib maintainer input; **defer** = not
for this PR.

| Status | EndKan name | Local path | Proposed Mathlib name | Proposed Mathlib path |
|--------|-------------|------------|----------------------|------------------------|
| ready | `endBifunctor` | `src/EndKan/End/Core.lean` | `Limits.endBifunctor` | `.../End/Diagonal.lean` |
| ready | `endBifunctor_obj_map` | Core | `endBifunctor_obj_map` | Diagonal |
| ready | `endBifunctor_map_app` | Core | `endBifunctor_map_app` | Diagonal |
| ready | `endBifunctor_obj_obj` | Core | `endBifunctor_obj_obj` | Diagonal |
| ready | `endBifunctor_fiber_obj` | Core | `endBifunctor_fiber_obj` | Diagonal |
| ready | `post_comp_endBifunctor_map` | Core | `post_comp_endBifunctor_map` | Diagonal |
| review | `DinaturalTransformation` | Core | `DiagonalWedge` or reuse `Wedge (endBifunctor F)` | Diagonal |
| review | `Cowedge` | Core | `DiagonalCowedge` or reuse `Cowedge` | Diagonal |
| alias | `EndObj` | Core | `endDiagonal` (abbrev `end_ (endBifunctor F)`) | Diagonal |
| alias | `π` | Core | `endDiagonal.π` or `end_.π (endBifunctor F)` | Diagonal |
| alias | `dinatural` | Core | doc-only / `Wedge.mk` packaging | Diagonal |
| alias | `lift` | Core | `end_.lift` on curried data | Diagonal |
| alias | `lift_π` | Core | `end_.lift_π` | Diagonal |
| alias | `uniq` | Core | `end_.hom_ext` | Diagonal |
| ready | `post_ext` | Core | `end_.post_ext` | Diagonal |
| ready | `post_uniq` | Core | `end_.post_uniq` | Diagonal |
| alias | `π_natural` | Core | `end_.condition` | Diagonal |
| alias | `map` | Core | `end_.map (curry.map α)` | Diagonal |
| alias | `map_π` | Core | `end_.map_π` | Diagonal |
| ready | `end_beta` | `src/EndKan/End/BetaEta.lean` | `endDiagonal.beta` | `.../End/BetaEta.lean` |
| ready | `end_eta` | BetaEta | `endDiagonal.eta` | BetaEta |
| ready | `end_π_beta` | BetaEta | `endDiagonal.π_beta` | BetaEta |
| defer | `end_π_eta` | BetaEta | — | trivial `rfl`; omit from PR |
| alias | `end_map_beta` | BetaEta | `end_.map_π` | omit or one-line alias |
| defer | `end_map_id` | BetaEta | — | use `end_.map_id` |
| defer | `end_map_comp` | BetaEta | — | use `end_.map_comp` |

## Dependency graph (Mathlib imports only)

```
Mathlib.CategoryTheory.Limits.Shapes.End          (existing)
Mathlib.CategoryTheory.Functor.Currying           (existing)
Mathlib.CategoryTheory.Products.Basic             (existing)
Mathlib.CategoryTheory.Opposites                  (existing)
        │
        ▼
Mathlib.CategoryTheory.Limits.Shapes.End.Diagonal  (new)
        │
        ▼
Mathlib.CategoryTheory.Limits.Shapes.End.BetaEta   (new)
        │
        ▼
Mathlib.CategoryTheory.Limits.Shapes.End.Examples  (new; no downstream imports)
```

## Not in scope for PR #1

- EndKan tactics (`end_beta`, `end_eta`, `endkan_beta`, …)
- Fubini (`EndKan.Fubini.*`)
- Concrete instance lemmas in `EndKan.Ends.EndTests` that rely on automation
- `end_π_eta` (reflexivity placeholder)
