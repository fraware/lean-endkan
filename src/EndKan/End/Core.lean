import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.Products
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers

namespace EndKan.End

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- A dinatural transformation from X to F is a family of morphisms
    ω_c : X ⟶ F(c,c) such that for any f : c ⟶ c', we have
    ω_c ≫ F.map (f, 𝟙 c') = ω_{c'} ≫ F.map (𝟙 c, f) -/
structure DinaturalTransformation (X : D) (F : Cᵒᵖ × C ⥤ D) where
  app : ∀ c : C, X ⟶ F.obj (op c, c)
  dinaturality : ∀ {c c' : C} (f : c ⟶ c'),
    app c ≫ F.map (op f, 𝟙 c') = app c' ≫ F.map (𝟙 c, f)

/-- The end of a functor F : Cᵒᵖ × C ⥤ D is the equalizer of two morphisms
    from ∏_{c} F(c,c) to ∏_{f : c ⟶ c'} F(c,c') -/
def EndObj (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D] : D :=
  wideEqualizer
    (Pi.lift fun c => F.map (𝟙 c, 𝟙 c))
    (Pi.lift fun f : Σ c c' : C, c ⟶ c' => F.map (op f.2.1, f.2.2))

/-- The projection from the end to F(c,c) -/
def End.π (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D] (c : C) :
  EndObj F ⟶ F.obj (op c, c) :=
  wideEqualizer.ι _ _ ≫ Pi.π _ c

/-- The end projections form a dinatural transformation -/
def End.dinatural (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D] :
  DinaturalTransformation (EndObj F) F where
  app := End.π F
  dinaturality := by
    intro c c' f
    apply wideEqualizer.hom_ext
    ext ⟨c₁, c₂, g⟩
    simp only [Category.assoc, wideEqualizer.condition, Pi.lift_π]
    congr 1
    simp only [Functor.map_comp, Category.assoc]
    rw [← F.map_comp]
    congr 1
    simp only [op_comp, op_id, Category.id_comp, Category.comp_id]

/-- Universal property of ends: any dinatural transformation factors uniquely through the end -/
def End.lift {F : Cᵒᵖ × C ⥤ D} [HasProductsOfShape C D] [HasWideEqualizers D]
    {X : D} (ω : DinaturalTransformation X F) : X ⟶ EndObj F :=
  wideEqualizer.lift (Pi.lift ω.app) (by
    ext ⟨c, c', f⟩
    simp only [Pi.lift_π, Category.assoc]
    rw [ω.dinaturality])

/-- The lifted morphism commutes with projections -/
theorem End.lift_π {F : Cᵒᵖ × C ⥤ D} [HasProductsOfShape C D] [HasWideEqualizers D]
    {X : D} (ω : DinaturalTransformation X F) (c : C) :
    End.lift ω ≫ End.π F c = ω.app c := by
  simp only [End.lift, End.π, Category.assoc, wideEqualizer.lift_ι, Pi.lift_π]

/-- Uniqueness of the lifted morphism -/
theorem End.uniq {F : Cᵒᵖ × C ⥤ D} [HasProductsOfShape C D] [HasWideEqualizers D]
    {X : D} (f g : X ⟶ EndObj F)
    (h : ∀ c : C, f ≫ End.π F c = g ≫ End.π F c) : f = g := by
  apply wideEqualizer.hom_ext
  ext c
  simp only [Category.assoc, wideEqualizer.condition, Pi.lift_π] at h
  exact h c

/-- The end as a limit -/
def End.asLimit (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D] :
  LimitCone (Discrete.functor fun c => F.obj (op c, c)) where
  cone := {
    pt := EndObj F
    π := Discrete.natTrans fun c => End.π F c.as
  }
  isLimit := {
    lift := fun s => End.lift {
      app := fun c => s.π.app ⟨c⟩
      dinaturality := by
        intro c c' g
        have h := s.π.naturality ⟨g⟩
        simp only [Discrete.functor_map, Discrete.natTrans_app] at h
        exact h
    }
    fac := by
      intro s c
      simp only [End.lift_π]
    uniq := by
      intro s f h
      apply End.uniq
      intro c
      exact h ⟨c⟩
  }

/-- Ends are preserved by functors -/
def End.map {F G : Cᵒᵖ × C ⥤ D} [HasProductsOfShape C D] [HasWideEqualizers D]
    (α : F ⟶ G) : EndObj F ⟶ EndObj G :=
  End.lift {
    app := fun c => End.π F c ≫ α.app (op c, c)
    dinaturality := by
      intro c c' f
      simp only [Category.assoc, α.naturality]
      rw [← Category.assoc, End.dinatural.dinaturality, Category.assoc]
      congr 1
      simp only [Functor.map_comp, Category.assoc]
      rw [← α.naturality]
      simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
  }

/-- Naturality of End.map -/
theorem End.map_π {F G : Cᵒᵖ × C ⥤ D} [HasProductsOfShape C D] [HasWideEqualizers D]
    (α : F ⟶ G) (c : C) :
    End.map α ≫ End.π G c = End.π F c ≫ α.app (op c, c) := by
  simp only [End.map, End.lift_π]

/-- Ends of constant functors -/
def End.const (X : D) [HasProductsOfShape C D] [HasWideEqualizers D] :
  EndObj (Functor.const (Cᵒᵖ × C) X) ≅ X :=
  { hom := End.lift {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    inv := End.π (Functor.const (Cᵒᵖ × C) X) (Classical.arbitrary C)
    hom_inv_id := by
      apply End.uniq
      intro c
      simp only [Category.assoc, End.lift_π, Category.id_comp]
    inv_hom_id := by simp }

/-- Ends of representable functors -/
def End.representable (c : C) [HasProductsOfShape C D] [HasWideEqualizers D] :
  EndObj (yoneda.obj c) ≅ 𝟙_ C :=
  { hom := End.lift {
      app := fun c' => 𝟙 (c ⟶ c')
      dinaturality := by simp
    }
    inv := End.π (yoneda.obj c) c
    hom_inv_id := by
      apply End.uniq
      intro c'
      simp only [Category.assoc, End.lift_π, Category.id_comp]
    inv_hom_id := by simp }

end EndKan.End
