import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Limits.Shapes.Initial
import Mathlib.CategoryTheory.Limits.Constructions.Coequalizers
import Mathlib.CategoryTheory.Limits.Constructions.Coproducts
import Mathlib.CategoryTheory.Limits.HasColimits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryCoproducts
import Mathlib.CategoryTheory.Limits.Shapes.WidePushouts
import Mathlib.CategoryTheory.Limits.Shapes.WideCoequalizers

namespace EndKan.Coend

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- A dinatural transformation from F to X is a family of morphisms
    ω_c : F(c,c) ⟶ X such that for any f : c ⟶ c', we have
    F.map (f, 𝟙 c') ≫ ω_{c'} = F.map (𝟙 c, f) ≫ ω_c -/
structure DinaturalTransformation (F : C × Cᵒᵖ ⥤ D) (X : D) where
  app : ∀ c : C, F.obj (c, op c) ⟶ X
  dinaturality : ∀ {c c' : C} (f : c ⟶ c'),
    F.map (f, 𝟙 c') ≫ app c' = F.map (𝟙 c, f) ≫ app c

/-- The coend of a functor F : C × Cᵒᵖ ⥤ D is the coequalizer of two morphisms
    from ∐_{f : c ⟶ c'} F(c,c') to ∐_{c} F(c,c) -/
def CoendObj (F : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D] : D :=
  wideCoequalizer
    (Sigma.desc fun f : Σ c c' : C, c ⟶ c' => F.map (f.2.1, op f.2.2))
    (Sigma.desc fun c => F.map (𝟙 c, 𝟙 c))

/-- The inclusion from F(c,c) to the coend -/
def Coend.ι (F : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D] (c : C) :
  F.obj (c, op c) ⟶ CoendObj F :=
  Sigma.ι _ c ≫ wideCoequalizer.π _ _

/-- The coend inclusions form a dinatural transformation -/
def Coend.dinatural (F : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D] :
  DinaturalTransformation F (CoendObj F) where
  app := Coend.ι F
  dinaturality := by
    intro c c' f
    apply wideCoequalizer.hom_ext
    ext ⟨c₁, c₂, g⟩
    simp only [Category.assoc, wideCoequalizer.condition, Sigma.ι_desc]
    congr 1
    simp only [Functor.map_comp, Category.assoc]
    rw [← F.map_comp]
    congr 1
    simp only [op_comp, op_id, Category.id_comp, Category.comp_id]

/-- Universal property of coends: any dinatural transformation factors uniquely through the coend -/
def Coend.desc {F : C × Cᵒᵖ ⥤ D} [HasCoproductsOfShape C D] [HasWideCoequalizers D]
    {X : D} (ω : DinaturalTransformation F X) : CoendObj F ⟶ X :=
  wideCoequalizer.desc (Sigma.desc ω.app) (by
    ext ⟨c, c', f⟩
    simp only [Sigma.ι_desc, Category.assoc]
    rw [ω.dinaturality])

/-- The descended morphism commutes with inclusions -/
theorem Coend.desc_ι {F : C × Cᵒᵖ ⥤ D} [HasCoproductsOfShape C D] [HasWideCoequalizers D]
    {X : D} (ω : DinaturalTransformation F X) (c : C) :
    Coend.ι F c ≫ Coend.desc ω = ω.app c := by
  simp only [Coend.ι, Coend.desc, Category.assoc, wideCoequalizer.π_desc, Sigma.ι_desc]

/-- Uniqueness of the descended morphism -/
theorem Coend.uniq {F : C × Cᵒᵖ ⥤ D} [HasCoproductsOfShape C D] [HasWideCoequalizers D]
    {X : D} (f g : CoendObj F ⟶ X)
    (h : ∀ c : C, Coend.ι F c ≫ f = Coend.ι F c ≫ g) : f = g := by
  apply wideCoequalizer.hom_ext
  ext c
  simp only [Category.assoc, wideCoequalizer.condition, Sigma.ι_desc] at h
  exact h c

/-- The coend as a colimit -/
def Coend.asColimit (F : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D] :
  ColimitCocone (Discrete.functor fun c => F.obj (c, op c)) where
  cocone := {
    pt := CoendObj F
    ι := Discrete.natTrans fun c => Coend.ι F c.as
  }
  isColimit := {
    desc := fun s => Coend.desc {
      app := fun c => s.ι.app ⟨c⟩
      dinaturality := by
        intro c c' g
        have h := s.ι.naturality ⟨g⟩
        simp only [Discrete.functor_map, Discrete.natTrans_app] at h
        exact h
    }
    fac := by
      intro s c
      simp only [Coend.desc_ι]
    uniq := by
      intro s f h
      apply Coend.uniq
      intro c
      exact h ⟨c⟩
  }

/-- Coends are preserved by functors -/
def Coend.map {F G : C × Cᵒᵖ ⥤ D} [HasCoproductsOfShape C D] [HasWideCoequalizers D]
    (α : F ⟶ G) : CoendObj F ⟶ CoendObj G :=
  Coend.desc {
    app := fun c => α.app (c, op c) ≫ Coend.ι G c
    dinaturality := by
      intro c c' f
      simp only [Category.assoc, α.naturality]
      rw [← Category.assoc, Coend.dinatural.dinaturality, Category.assoc]
      congr 1
      simp only [Functor.map_comp, Category.assoc]
      rw [← α.naturality]
      simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
  }

/-- Naturality of Coend.map -/
theorem Coend.map_ι {F G : C × Cᵒᵖ ⥤ D} [HasCoproductsOfShape C D] [HasWideCoequalizers D]
    (α : F ⟶ G) (c : C) :
    Coend.ι F c ≫ Coend.map α = α.app (c, op c) ≫ Coend.ι G c := by
  simp only [Coend.map, Coend.desc_ι]

/-- Coends of constant functors -/
def Coend.const (X : D) [HasCoproductsOfShape C D] [HasWideCoequalizers D] :
  CoendObj (Functor.const (C × Cᵒᵖ) X) ≅ X :=
  { hom := Coend.desc {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    inv := Coend.ι (Functor.const (C × Cᵒᵖ) X) (Classical.arbitrary C)
    hom_inv_id := by simp
    inv_hom_id := by
      apply Coend.uniq
      intro c
      simp only [Category.assoc, Coend.desc_ι, Category.comp_id] }

/-- Coends of representable functors -/
def Coend.representable (c : C) [HasCoproductsOfShape C D] [HasWideCoequalizers D] :
  CoendObj (coyoneda.obj c) ≅ 𝟙_ C :=
  { hom := Coend.desc {
      app := fun c' => 𝟙 (c' ⟶ c)
      dinaturality := by simp
    }
    inv := Coend.ι (coyoneda.obj c) c
    hom_inv_id := by simp
    inv_hom_id := by
      apply Coend.uniq
      intro c'
      simp only [Category.assoc, Coend.desc_ι, Category.comp_id] }

end EndKan.Coend
