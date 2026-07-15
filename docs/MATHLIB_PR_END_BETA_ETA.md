# Mathlib design proposal for a minimal diagonal-end adapter

## Proposed discussion title

`Curried adapter for profunctors on Cᵒᵖ × C in the end API`

## Decision

The first upstream discussion is narrowed to one adapter and three general object and map equations. The dedicated diagonal-end object, wedge structure, universal morphism wrappers, β and η aliases, and namespace layer remain outside the initial proposal.

The candidate compiles on Lean and Mathlib `v4.31.0` and is exercised against the existing Fubini layer.

## Problem addressed

Mathlib's end API consumes a functor of type `Cᵒᵖ ⥤ C ⥤ D`, while profunctor developments commonly start from `F : Cᵒᵖ × C ⥤ D`. Users repeatedly expose `curry.obj F` and state equations connecting the curried objects and maps to product-category expressions.

The proposed declarations address that interface while preserving Mathlib's existing `end_`, `end_.π`, `end_.lift`, `end_.lift_π`, `end_.condition`, `end_.hom_ext`, and `end_.map` declarations as the universal-property API.

## Proposed declarations

```lean
abbrev endBifunctor (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ ⥤ C ⥤ D :=
  curry.obj F

@[simp] theorem endBifunctor_fiber_obj ...
@[simp] theorem endBifunctor_obj_map ...
@[simp] theorem endBifunctor_map_app ...
```

The diagonal object equation is a specialization of `endBifunctor_fiber_obj` and stays as an example or local corollary.

## Scope excluded from the first discussion

The following EndKan declarations are deferred because Mathlib already provides their mathematical content or because their design requires independent evidence.

- `DinaturalTransformation` and `Cowedge`
- `EndObj`, `π`, `dinatural`, `lift`, `lift_π`, and `uniq`
- `post_ext` and `post_uniq`
- `map` and `map_π`
- `end_beta`, `end_eta`, `end_π_beta`, and `end_map_beta`
- a dedicated `endDiagonal` namespace or new `End/` directory
- tactics, attributes, telemetry, Fubini theorems, and concrete instances

## Downstream evidence

`src/Scratch/MathlibEndBifunctorConsumer.lean` validates two uses.

1. `EndKan.Fubini.end_fubini_beta` reduces directly to Mathlib's existing `end_.lift_π` once `endBifunctor` supplies the expected functor type.
2. `EndKan.Fubini.Slice` restates three object and map equations for product indices. Each equation is an instance of the proposed general declarations, including the off-diagonal object equation used by slices.

The off-diagonal consumer supports retaining `endBifunctor_fiber_obj` and deriving the diagonal-only `endBifunctor_obj_obj` theorem locally. The resulting review surface contains four declarations.

## Evidence boundary

Validation rejected a stronger claim that the proposed simp lemmas would automatically normalize an entire dependent dinaturality equality into product form.

After map simplification, Lean retained a hom target expressed through `curry.obj F`, while the proposed goal used `F.obj (op c, c')`. Resolving that whole equation would require additional dependent transport or a different statement. The candidate contains neither, and the proposal claims utility only for the isolated equations demonstrated by the Fubini slice consumer.

This limitation also makes the `simp` attributes a maintainer-review question instead of a settled design choice.

## Before and after proof

The existing consumer reaches β reduction through EndKan wrappers.

```lean
EndKan.Fubini.end_fubini_beta f h c
```

The narrowed interface reaches the same universal-property result through Mathlib.

```lean
exact Limits.end_.lift_π
  (F := endBifunctor F) f (fun _ _ g => h g) c
```

The adapter aligns the product-category profunctor with Mathlib's existing end API. This consumer provides no evidence for a new β theorem.

## Proposed placement

The preferred initial placement is the existing `Mathlib/CategoryTheory/Limits/Shapes/End.lean` module unless maintainers prefer a small adjacent module. Four declarations do not yet justify a new hierarchy.

## Validated gates

- `lake build Scratch.MathlibEndBifunctorConsumer` passes on Lean and Mathlib `v4.31.0`
- `lake build EndKan` passes in pull-request CI
- the candidate contains one adapter and three equations
- the Fubini β proof uses `end_.lift_π` directly
- the three Fubini slice equations instantiate the proposed general equations
- the candidate introduces no structure, typeclass, end object alias, projection, lift, map, β theorem, η theorem, or dependent transport
- the unsupported whole-equation simp claim is excluded

## Maintainer questions

1. Does Mathlib want a named adapter for profunctors presented as `Cᵒᵖ × C ⥤ D`?
2. Which, if any, of the three demonstrated equations belong in the public API and should carry `simp`?
3. Should the accepted declarations live in `End.lean`, an adjacent module, or a more general currying API?

## Current status

The candidate is mechanically validated and remains `ESCALATE AND NARROW`. A focused maintainer discussion should determine whether the upstream surface contains four declarations, the adapter alone, or no new API.
