# Draft Mathlib design discussion

I am preparing a small contribution around ends of profunctors presented as functors `F : Cᵒᵖ × C ⥤ D`.

Mathlib's existing end API is expressed for `Cᵒᵖ ⥤ C ⥤ D`. In downstream work, the recurring friction is the conversion through `curry.obj F` and the repetition of equations connecting the curried objects and maps to product-category expressions.

The current candidate is intentionally limited to the following surface.

```lean
abbrev endBifunctor (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ ⥤ C ⥤ D :=
  curry.obj F

@[simp] theorem endBifunctor_fiber_obj ...
@[simp] theorem endBifunctor_obj_map ...
@[simp] theorem endBifunctor_map_app ...
```

A Fubini consumer provides two pieces of evidence.

- Its β computation closes directly with the existing `Limits.end_.lift_π` theorem once the adapter supplies the expected functor shape.
- Its slice layer currently restates three object and map equations that are direct instances of the proposed declarations, including an off-diagonal object equation.

Validation also found an important limit. Rewriting the map terms in a full dependent dinaturality equality did not automatically identify the hom target expressed through `curry.obj F` with the corresponding `F.obj` target. The candidate therefore claims value for the isolated equations demonstrated by the slice consumer and does not introduce transports or a higher-level diagonal-end abstraction.

The broader API remains deferred, including new wedge structures, end object aliases, projections, lifts, map wrappers, β and η aliases, and a dedicated namespace.

The focused questions are whether Mathlib wants a named adapter of this form, which of the three equations should be public and tagged `simp`, and whether accepted declarations belong in `CategoryTheory/Limits/Shapes/End.lean`, an adjacent module, or a more general currying API.

The candidate and its Fubini consumer build on Lean and Mathlib `v4.31.0`.
