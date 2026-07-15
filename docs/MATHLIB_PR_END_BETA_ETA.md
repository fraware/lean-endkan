# Mathlib PR proposal for a minimal diagonal-end adapter

## Proposed PR title

`feat(CategoryTheory/Limits): add a curried adapter for profunctors on Cᵒᵖ × C`

## Decision

The first upstream proposal is narrowed to one adapter and three general simplification lemmas. The dedicated diagonal-end object, wedge structure, universal morphism wrappers, β and η aliases, and namespace layer remain outside the initial PR.

This scope follows a direct comparison with Mathlib's existing end API and a downstream test against `EndKan.Fubini`.

## Problem addressed

Mathlib's end API consumes a functor of type `Cᵒᵖ ⥤ C ⥤ D`, while profunctor developments commonly start from `F : Cᵒᵖ × C ⥤ D`. Users repeatedly expose `curry.obj F` and normalize its objects and maps back to product-category expressions.

The proposed declarations remove that interface friction while preserving Mathlib's existing `end_`, `end_.π`, `end_.lift`, `end_.lift_π`, `end_.condition`, `end_.hom_ext`, and `end_.map` APIs as the canonical universal-property layer.

## Proposed declarations

```lean
abbrev endBifunctor (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ ⥤ C ⥤ D :=
  curry.obj F

@[simp] theorem endBifunctor_fiber_obj ...
@[simp] theorem endBifunctor_obj_map ...
@[simp] theorem endBifunctor_map_app ...
```

The diagonal object equation is a specialization of `endBifunctor_fiber_obj` and stays as an example or local corollary.

## Scope excluded from the first PR

The following EndKan declarations are deferred because Mathlib already provides their mathematical content or because their library design requires separate maintainer agreement.

- `DinaturalTransformation` and `Cowedge`
- `EndObj`, `π`, `dinatural`, `lift`, `lift_π`, and `uniq`
- `post_ext` and `post_uniq`
- `map` and `map_π`
- `end_beta`, `end_eta`, `end_π_beta`, and `end_map_beta`
- a dedicated `endDiagonal` namespace or new `End/` directory
- tactics, attributes, telemetry, Fubini theorems, and concrete instances

## Downstream evidence

`src/Scratch/MathlibEndBifunctorConsumer.lean` tests the candidate against two current uses.

1. `EndKan.Fubini.end_fubini_beta` reduces directly to Mathlib's existing `end_.lift_π` once `endBifunctor` supplies the expected functor type.
2. `EndKan.Fubini.Slice` currently restates object and map normalizations for product indices. The three proposed simplification lemmas cover those rewrites, including the off-diagonal object equation used by slices.

This evidence changes the provisional declaration set in one respect. The general `endBifunctor_fiber_obj` lemma is retained, while the diagonal-only `endBifunctor_obj_obj` lemma is derived locally. The public surface remains four declarations in total.

## Before and after proof

The existing consumer reaches β reduction through EndKan wrappers.

```lean
EndKan.Fubini.end_fubini_beta f h c
```

The narrowed interface reaches the same universal-property result through Mathlib.

```lean
exact Limits.end_.lift_π (F := endBifunctor F) f h c
```

The improvement comes from aligning a product-category profunctor with the input shape expected by Mathlib. No additional β theorem is required for this consumer.

## Proposed placement

The preferred initial placement is the existing `Mathlib/CategoryTheory/Limits/Shapes/End.lean` module unless maintainers prefer a small adjacent module. The four declarations do not justify a new hierarchy on their own.

## Acceptance gates

- `lake build Scratch.MathlibEndBifunctorConsumer`
- `lake build EndKan`
- the candidate contains exactly one adapter and three public simplification lemmas
- the downstream Fubini proof uses `end_.lift_π` directly
- the product-category normal form closes with the candidate simp lemmas
- no new structure, typeclass, end object alias, projection, lift, map, or β and η declaration enters the first PR
- no duplicated public diagonal object lemma is introduced
- a Mathlib maintainer confirms naming and placement before code submission

## Primary maintainer question

Does Mathlib want a named `endBifunctor` adapter for profunctors on `Cᵒᵖ × C`, together with the three general object and map simplification lemmas demonstrated by the Fubini consumer?

## Current status

The proposal remains `ESCALATE AND NARROW` until the candidate builds on the pinned Mathlib `v4.31.0` environment and receives a maintainer answer on naming and placement.
