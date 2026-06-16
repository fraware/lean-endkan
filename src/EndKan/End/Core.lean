import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Opposites

namespace EndKan.End

open CategoryTheory
open CategoryTheory.Functor
open Opposite
open scoped Prod

universe u v

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]

/-- The curried form of a functor `Cᵒᵖ × C ⥤ D`, as used by Mathlib's `end_`. -/
abbrev endBifunctor (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ ⥤ C ⥤ D :=
  curry.obj F

@[simp]
theorem endBifunctor_obj_map {F : Cᵒᵖ × C ⥤ D} (c : C) (f : c ⟶ c') :
    ((endBifunctor F).obj (op c)).map f = F.map (𝟙 (op c) ×ₘ f) := by
  simp [endBifunctor]

@[simp]
theorem endBifunctor_map_app {F : Cᵒᵖ × C ⥤ D} {c c' : C} (f : c ⟶ c') :
    ((endBifunctor F).map f.op).app c' = F.map (f.op ×ₘ 𝟙 c') := by
  simp [endBifunctor]

@[simp]
theorem endBifunctor_obj_obj {F : Cᵒᵖ × C ⥤ D} (c : C) :
    ((endBifunctor F).obj (op c)).obj c = F.obj (op c, c) := by
  simp [endBifunctor]

@[simp]
theorem endBifunctor_fiber_obj {F : Cᵒᵖ × C ⥤ D} (c c' : C) :
    ((endBifunctor F).obj (op c)).obj c' = F.obj (op c, c') := by
  simp [endBifunctor]

theorem post_comp_endBifunctor_map {F : Cᵒᵖ × C ⥤ D} {c c' : C} (f : c ⟶ c')
    {X : D} (h : X ⟶ F.obj (op c, c)) :
    h ≫ ((endBifunctor F).obj (op c)).map f = h ≫ F.map (𝟙 (op c) ×ₘ f) := by
  conv_rhs => rw [← endBifunctor_obj_map]
  rfl

/-- A dinatural transformation from `X` into `F`, expressed via the curried bifunctor. -/
structure DinaturalTransformation (X : D) (F : Cᵒᵖ × C ⥤ D) where
  app : ∀ c : C, X ⟶ F.obj (op c, c)
  dinaturality : ∀ {c c' : C} (f : c ⟶ c'),
    app c ≫ ((endBifunctor F).obj (op c)).map f =
      app c' ≫ ((endBifunctor F).map f.op).app c'

/-- The end of `F`, defined via Mathlib's `CategoryTheory.Limits.end_`. -/
noncomputable def EndObj (F : Cᵒᵖ × C ⥤ D) [Limits.HasEnd (endBifunctor F)] : D :=
  Limits.end_ (endBifunctor F)

/-- Projection from the end to the diagonal object `F(c, c)`. -/
noncomputable def π (F : Cᵒᵖ × C ⥤ D) [Limits.HasEnd (endBifunctor F)] (c : C) :
    EndObj F ⟶ F.obj (op c, c) := by
  simpa [EndObj, endBifunctor] using Limits.end_.π (endBifunctor F) c

/-- The end projections form a dinatural transformation. -/
noncomputable def dinatural (F : Cᵒᵖ × C ⥤ D) [Limits.HasEnd (endBifunctor F)] :
    DinaturalTransformation (EndObj F) F where
  app := π F
  dinaturality := by
    intro c c' f
    dsimp [π]
    exact Limits.end_.condition (endBifunctor F) f

/-- Universal property of ends. -/
noncomputable def lift {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    {X : D} (ω : DinaturalTransformation X F) : X ⟶ EndObj F :=
  Limits.end_.lift (fun c => ω.app c) (fun _ _ f => ω.dinaturality (f := f))

@[reassoc (attr := simp)]
theorem lift_π {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    {X : D} (ω : DinaturalTransformation X F) (c : C) :
    lift ω ≫ π F c = ω.app c := by
  dsimp [lift, π, EndObj]
  exact Limits.end_.lift_π (F := endBifunctor F) _ _ c

theorem uniq {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    {X : D} (f g : X ⟶ EndObj F)
    (h : ∀ c : C, f ≫ π F c = g ≫ π F c) : f = g := by
  simpa [EndObj, endBifunctor] using Limits.end_.hom_ext (f := f) (g := g) h

/-- A dinatural transformation from `F` into `X` (cowedge data; mirrors `Limits.Cowedge`). -/
structure Cowedge (F : Cᵒᵖ × C ⥤ D) (X : D) where
  app : ∀ c : C, F.obj (op c, c) ⟶ X
  dinaturality : ∀ {c c' : C} (f : c ⟶ c'),
    ((endBifunctor F).map f.op).app c ≫ app c =
      ((endBifunctor F).obj (op c')).map f ≫ app c'

/-- Morphisms `EndObj F ⟶ X` are determined by precomposition with every `Y ⟶ EndObj F`
    (Yoneda / covariant hom). Dual to `uniq` for maps into the end. -/
theorem post_ext {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    {X : D} {f g : EndObj F ⟶ X}
    (h : ∀ (Y : D) (y : Y ⟶ EndObj F), y ≫ f = y ≫ g) : f = g := by
  simpa using h (EndObj F) (𝟙 _)

/-- Alias for `post_ext` (maps from the end). -/
theorem post_uniq {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    {X : D} {f g : EndObj F ⟶ X}
    (h : ∀ (Y : D) (y : Y ⟶ EndObj F), y ≫ f = y ≫ g) : f = g :=
  post_ext h

@[reassoc (attr := simp)]
theorem π_natural {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    {c c' : C} (f : c ⟶ c') :
    π F c ≫ ((endBifunctor F).obj (op c)).map f =
      π F c' ≫ ((endBifunctor F).map f.op).app c' := by
  dsimp [π]
  exact Limits.end_.condition (endBifunctor F) f

/-- A natural transformation induces a morphism between ends. -/
noncomputable def map {F G : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    [Limits.HasEnd (endBifunctor G)] (α : F ⟶ G) : EndObj F ⟶ EndObj G :=
  Limits.end_.map (curry.map α)

@[reassoc (attr := simp)]
theorem map_π {F G : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    [Limits.HasEnd (endBifunctor G)] (α : F ⟶ G) (c : C) :
    map α ≫ π G c = π F c ≫ α.app (op c, c) := by
  simp only [map, π, EndObj, endBifunctor, curry_map_app_app]
  exact Limits.end_.map_π (curry.map α) c

end EndKan.End
