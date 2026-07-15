# Proposed Mathlib placement for the minimal adapter

## Preferred first placement

The narrowed proposal should initially live in `Mathlib/CategoryTheory/Limits/Shapes/End.lean`, close to the existing `end_` API.

The candidate adds four declarations and does not introduce a new mathematical object or universal property. A dedicated `End/Diagonal.lean` hierarchy would create more navigation and naming surface than the current evidence supports.

```lean
namespace CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D]

/-- Curried form of a profunctor `Cᵒᵖ × C ⥤ D`, as consumed by the end API. -/
abbrev endBifunctor (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ ⥤ C ⥤ D :=
  curry.obj F

@[simp] theorem endBifunctor_fiber_obj ...
@[simp] theorem endBifunctor_obj_map ...
@[simp] theorem endBifunctor_map_app ...

end CategoryTheory.Limits
```

## Import boundary

The implementation needs the existing end module together with currying, products, and opposites. It should avoid imports from `lean-endkan` and should add no new typeclass assumptions.

## Naming boundary

The first PR asks maintainers to decide only two points.

1. Whether `endBifunctor` is an acceptable name for the curried profunctor adapter.
2. Whether the declarations belong in `End.lean` or a small adjacent module.

The proposal deliberately leaves `DiagonalWedge`, `endDiagonal`, dedicated projections and lifts, β and η aliases, and a diagonal-end namespace for later evidence.

## Expansion rule

A later module split or namespace layer requires multiple accepted downstream consumers whose proofs remain materially clearer after introducing the additional abstraction. The initial Fubini consumer supports the adapter and its normalization lemmas only.
