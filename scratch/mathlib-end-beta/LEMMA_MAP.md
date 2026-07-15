# Minimal diagonal-end adapter declaration map

This map records the narrowed first Mathlib proposal from `lean-endkan`. The target environment is Lean and Mathlib `v4.31.0`.

## Existing Mathlib surface

Mathlib already provides the universal-property layer for ends.

| Existing declaration family | Role |
|---|---|
| `Limits.end_`, `Limits.end_.π`, `Limits.end_.lift` | End object, projections, and mediating morphisms |
| `Limits.end_.lift_π`, `Limits.end_.condition`, `Limits.end_.hom_ext` | Computation, wedge compatibility, and uniqueness |
| `Limits.end_.map`, `Limits.end_.map_π`, `Limits.end_.map_id`, `Limits.end_.map_comp` | Functoriality |

## Candidate public declarations

| Decision | Candidate | Evidence |
|---|---|---|
| include | `endBifunctor` | Bridges `Cᵒᵖ × C ⥤ D` to the functor shape consumed by `end_` |
| include | `endBifunctor_fiber_obj` | Covers diagonal and off-diagonal object rewrites; used by Fubini slices |
| include | `endBifunctor_obj_map` | Normalizes the covariant map component to a product morphism |
| include | `endBifunctor_map_app` | Normalizes the contravariant natural-transformation component |
| derive locally | `endBifunctor_obj_obj` | Special case of `endBifunctor_fiber_obj` with equal indices |

The initial public surface contains four declarations in total.

## Deferred or rejected declarations

| Decision | EndKan declaration | Reason |
|---|---|---|
| defer | `DinaturalTransformation` | Competes with Mathlib's existing `Wedge` representation and needs a separate design decision |
| defer | `Cowedge` | Dual packaging is outside the adapter question |
| reject for PR 1 | `EndObj`, `π`, `dinatural`, `lift`, `lift_π`, `uniq` | Thin wrappers around existing Mathlib declarations |
| reject for PR 1 | `post_ext`, `post_uniq` | No demonstrated need in the selected consumer |
| reject for PR 1 | `map`, `map_π` | Existing `end_.map` and `end_.map_π` provide the content |
| reject for PR 1 | `end_beta`, `end_eta`, `end_π_beta`, `end_map_beta` | The Fubini consumer closes directly with existing Mathlib theorems |
| reject | `end_π_eta` | Reflexivity only |
| reject for PR 1 | `end_map_id`, `end_map_comp` | Existing `end_.map_id` and `end_.map_comp` provide the content |
| defer | dedicated `endDiagonal` namespace and modules | The four-declaration surface does not yet justify a new hierarchy |

## Downstream evidence

The candidate is exercised in `src/Scratch/MathlibEndBifunctorConsumer.lean`.

- The β obligation represented by `EndKan.Fubini.end_fubini_beta` closes with `Limits.end_.lift_π`.
- The three local normalization lemmas near the top of `EndKan.Fubini.Slice` are covered by the candidate object and map equations.
- The general fiber equation makes a separate diagonal object simp theorem unnecessary in the first PR.

## Decision rule

Any declaration added beyond this map requires a named downstream theorem that becomes materially shorter, clearer, or more stable under Mathlib's existing abstractions. Build success alone does not satisfy this rule.
