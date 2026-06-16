import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Opposites
import EndKan.End.Core

namespace EndKan.End

open CategoryTheory
open CategoryTheory.Functor
open Opposite

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]

/-- β-reduction for ends: composing through `π` with the curried action simplifies. -/
theorem end_beta {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)] {X : D}
    (f : ∀ c : C, X ⟶ F.obj (op c, c))
    (h : ∀ {c c' : C} (g : c ⟶ c'),
      f c ≫ ((endBifunctor F).obj (op c)).map g =
        f c' ≫ ((endBifunctor F).map g.op).app c')
    (c : C) :
    lift ⟨f, h⟩ ≫ π F c = f c :=
  lift_π _ c

/-- η-expansion for ends: uniqueness of the mediating morphism. -/
theorem end_eta {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)] {X : D} (f : X ⟶ EndObj F) :
    f = lift ⟨(fun c => f ≫ π F c), (by
      intro c c' g
      simp only [Category.assoc, π_natural])⟩ := by
  symm
  apply uniq
  intro c
  simp only [Category.assoc, lift_π]

@[reassoc (attr := simp)]
theorem end_π_beta {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)] {c c' : C} (f : c ⟶ c') :
    π F c ≫ ((endBifunctor F).obj (op c)).map f =
      π F c' ≫ ((endBifunctor F).map f.op).app c' :=
  π_natural (F := F) f

theorem end_π_eta {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)] (c : C) :
    π F c = π F c := rfl

@[reassoc (attr := simp)]
theorem end_map_beta {F G : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    [Limits.HasEnd (endBifunctor G)] (α : F ⟶ G) (c : C) :
    map α ≫ π G c = π F c ≫ α.app (op c, c) :=
  map_π α c

theorem end_map_id {F : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)] :
    map (𝟙 F) = 𝟙 (EndObj F) := by
  dsimp [map, EndObj, endBifunctor]
  exact Limits.end_.map_id (F := endBifunctor F)

@[reassoc (attr := simp)]
theorem end_map_comp {F G H : Cᵒᵖ × C ⥤ D} [Limits.HasEnd (endBifunctor F)]
    [Limits.HasEnd (endBifunctor G)] [Limits.HasEnd (endBifunctor H)] (α : F ⟶ G) (β : G ⟶ H) :
    map α ≫ map β = map (α ≫ β) := by
  simp only [map]
  exact Limits.end_.map_comp (curry.map α) (curry.map β)

end EndKan.End
