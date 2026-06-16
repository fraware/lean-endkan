# Draft Mathlib module structure — coend β/η

Proposed layout under `Mathlib/CategoryTheory/Limits/Shapes/Coend/` (new **directory**
alongside coend definitions in existing `End.lean` / related modules).

## `Diagonal.lean`

Namespace: `CategoryTheory.Limits` (extend existing `coend` section).

```lean
/-!
# Coends of profunctors on `C × Cᵒᵖ`

Thin diagonal API over `coend` for functors `F : C × Cᵒᵖ ⥤ E`, via swap + currying to
`Cᵒᵖ ⥤ C ⥤ E`.
-/

variable {C E : Type*} [Category C] [Category E]

/-- Swap `C × Cᵒᵖ` to `Cᵒᵖ × C` for currying. -/
abbrev coendSwap (F : C × Cᵒᵖ ⥤ E) : Cᵒᵖ × C ⥤ E := Prod.swap Cᵒᵖ C ⋙ F

/-- Curried form of a profunctor `C × Cᵒᵖ ⥤ E`, as used by `coend`. -/
noncomputable def coendBifunctor (F : C × Cᵒᵖ ⥤ E) : Cᵒᵖ ⥤ C ⥤ E :=
  curry.obj (coendSwap F)

-- @[simp] fiber lemmas: coendDiagonal, coendBifunctor_map_app, coendBifunctor_obj_map, ...

/-- Dinaturality data for a profunctor on `C × Cᵒᵖ`, expressed on the diagonal. -/
structure DiagonalDinaturality (F : C × Cᵒᵖ ⥤ E) (X : E) where
  app : ∀ c : C, ((coendBifunctor F).obj (op c)).obj c ⟶ X
  dinaturality : ∀ {c c' : C} (f : c ⟶ c'), ...

def DiagonalDinaturality.ofDiagonal (f : ∀ c, F.obj (c, op c) ⟶ X) (h : ...) : ...

/-- The coend of `F : C × Cᵒᵖ ⥤ E`. -/
noncomputable abbrev coendDiagonal (F : C × Cᵒᵖ ⥤ E) [HasCoend (coendBifunctor F)] : E :=
  coend (coendBifunctor F)

namespace coendDiagonal

noncomputable def ιCurry ...
noncomputable def ι ...       -- diagonal F(c, op c) ⟶ coendDiagonal F
noncomputable def desc ...
theorem ι_desc ...
theorem hom_ext ...           -- from coend.hom_ext
noncomputable def map ...

end coendDiagonal
```

Design notes:

- Prefer `coendDiagonal` over `CoendObj` (Mathlib uses lowercase `coend`).
- `coendSwap` is needed because profunctors are `C × Cᵒᵖ` but `curry` expects `Cᵒᵖ × C`.
- `DiagonalDinaturality` avoids clashing with existing dinaturality on curried functors;
  alternatively expose `def diagonalDinaturality (F) := ...` with simp lemmas relating `app`
  to `F.obj (c, op c)`.
- `eqToHom_symm_comp_mpr_diagonal` bridges curried hom-types and diagonal objects; keep in
  Diagonal (not BetaEta).

## `BetaEta.lean`

```lean
/-!
# β/η rules for diagonal coends

`beta` / `eta` lemmas for rewriting through `coendDiagonal.ι` and `coendDiagonal.desc`.
-/

namespace coendDiagonal

theorem beta {F : C × Cᵒᵖ ⥤ E} ... :
    ι F c ≫ desc ω = f c := ...

theorem eta {F : C × Cᵒᵖ ⥤ E} {X : E} (f : coendDiagonal F ⟶ X) :
    f = desc ⟨(fun c => ιCurry F c ≫ f), ...⟩ := ...

@[reassoc (attr := simp)]
theorem ι_beta {F : C × Cᵒᵖ ⥤ E} {c c' : C} (f : c ⟶ c') :
    F.map (𝟙 c ×ₘ f.op) ≫ ι F c = F.map (f ×ₘ 𝟙 (op c')) ≫ ι F c' := ...

end coendDiagonal
```

Do **not** duplicate `coend.map_id`; link in module docstring.
Do **not** upstream `ι_eta` (reflexivity).

## `Examples.lean`

Abstract-category examples only (no `endkan_beta` / tactics). See
`src/Scratch/MathlibCoendBetaExamples.lean` in this repo for a buildable mirror using
`EndKan.Coend` lemmas.

Suggested Mathlib examples:

1. β-reduction for a manually built dinatural family (`ofDiagonal`).
2. η-expansion recovering a morphism out of the coend.
3. Dinaturality of `ι` along a morphism (`ι_beta`).
4. Functoriality along a profunctor transformation (via `map_ιCurry` + `ιCurry`).

## Import policy

- `Diagonal.lean` imports existing coend API + currying/products/whiskering/eqToHom.
- `BetaEta.lean` imports `Diagonal.lean` only.
- `Examples.lean` imports `BetaEta.lean`; not imported by any other Mathlib module.
