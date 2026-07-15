# Draft Mathlib design discussion

I am preparing a small contribution around ends of profunctors presented as functors `F : Cᵒᵖ × C ⥤ D`.

Mathlib's existing end API is expressed for `Cᵒᵖ ⥤ C ⥤ D`. In downstream work, the recurring friction is the conversion through `curry.obj F` and the normalization of the resulting objects and maps back to product-category expressions.

The current candidate is intentionally limited to the following surface.

```lean
abbrev endBifunctor (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ ⥤ C ⥤ D :=
  curry.obj F

@[simp] theorem endBifunctor_fiber_obj ...
@[simp] theorem endBifunctor_obj_map ...
@[simp] theorem endBifunctor_map_app ...
```

A real Fubini consumer provides two pieces of evidence.

- Its β computation closes directly with the existing `Limits.end_.lift_π` theorem once the adapter supplies the expected functor shape.
- Its slice layer currently restates the same off-diagonal object and map normalization equations covered by the proposed simp lemmas.

I have therefore deferred the broader diagonal-end API, including new wedge structures, end object aliases, projections, lifts, map wrappers, β and η aliases, and a dedicated namespace.

The focused design question is whether Mathlib would welcome a named adapter of this form and, if so, whether the four declarations should live in the existing `CategoryTheory/Limits/Shapes/End.lean` module or a small adjacent module.

A secondary question is whether `endBifunctor` is the right name, or whether the community prefers a name that emphasizes currying or diagonal evaluation.
