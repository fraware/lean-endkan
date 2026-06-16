# Draft Mathlib module structure — end β/η

Proposed layout under `Mathlib/CategoryTheory/Limits/Shapes/End/` (new **directory**
alongside the existing `End.lean` file; the file may later be renamed `Basic.lean` in a
separate Mathlib refactor).

## `Diagonal.lean`

Namespace: `CategoryTheory.Limits` (extend existing `End` section).

```lean
/-!
# Ends of profunctors on `Cᵒᵖ × C`

Thin diagonal API over `end_` for functors `F : Cᵒᵖ × C ⥤ D`, via currying to
`Cᵒᵖ ⥤ C ⥤ D`.
-/

variable {C D : Type*} [Category C] [Category D]

/-- Curried form of a profunctor `Cᵒᵖ × C ⥤ D`, as used by `end_`. -/
noncomputable def endBifunctor (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ ⥤ C ⥤ D := curry.obj F

-- @[simp] fiber lemmas: endBifunctor_obj_map, endBifunctor_map_app, ...

/-- Wedge data for a profunctor on `Cᵒᵖ × C`, expressed on the diagonal. -/
structure DiagonalWedge (X : D) (F : Cᵒᵖ × C ⥤ D) where
  app : ∀ c : C, X ⟶ F.obj (op c, c)
  dinaturality : ∀ {c c' : C} (f : c ⟶ c'), ...

/-- The end of `F : Cᵒᵖ × C ⥤ D`. -/
noncomputable abbrev endDiagonal (F : Cᵒᵖ × C ⥤ D) [HasEnd (endBifunctor F)] : D :=
  end_ (endBifunctor F)

namespace endDiagonal

noncomputable def π ... 
noncomputable def lift ...
theorem lift_π ...
theorem hom_ext ...    -- from end_.hom_ext
theorem post_ext ...   -- morphisms out of the end
theorem map ...

end endDiagonal
```

Design notes:

- Prefer `endDiagonal` over `EndObj` (Mathlib uses lowercase `end_`).
- `DiagonalWedge` avoids clashing with the existing `Wedge F` for `F : Jᵒᵖ ⥤ J ⥤ C`;
  alternatively expose `def diagonalWedge (F) := Wedge (endBifunctor F)` with simp lemmas
  relating `app` to `F.obj (op c, c)`.
- `Cowedge` dual packaging is optional for PR #1 if reviewers prefer only wedge data.

## `BetaEta.lean`

```lean
/-!
# β/η rules for diagonal ends

`beta` / `eta` lemmas for rewriting through `endDiagonal.π` and `endDiagonal.lift`.
-/

namespace endDiagonal

theorem beta {F : Cᵒᵖ × C ⥤ D} ... :
    lift ω ≫ π F c = ω.app c := lift_π ...

theorem eta {F : Cᵒᵖ × C ⥤ D} {X : D} (f : X ⟶ endDiagonal F) :
    f = lift ⟨(fun c => f ≫ π F c), ...⟩ := ...

@[reassoc (attr := simp)]
theorem π_beta {F : Cᵒᵖ × C ⥤ D} {c c' : C} (f : c ⟶ c') :
    π F c ≫ (endBifunctor F).obj (op c).map f =
      π F c' ≫ (endBifunctor F).map f.op |>.app c' := ...

end endDiagonal
```

Do **not** duplicate `end_.map_id` / `end_.map_comp`; link in module docstring.

## `Examples.lean`

Abstract-category examples only (no `endkan_beta` / tactics). See
`src/Scratch/MathlibEndBetaExamples.lean` in this repo for a buildable mirror using
`EndKan.End` lemmas.

Suggested Mathlib examples:

1. β-reduction for a manually built dinatural family.
2. η-expansion recovering a morphism into the end.
3. Naturality of `end_.map` along a profunctor transformation (via `π_beta` + `beta`).

## Import policy

- `Diagonal.lean` imports existing `End.lean` + currying/products.
- `BetaEta.lean` imports `Diagonal.lean` only.
- `Examples.lean` imports `BetaEta.lean`; not imported by any other Mathlib module.
