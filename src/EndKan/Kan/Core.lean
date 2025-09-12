import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.Coequalizers
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.HasColimits
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.WideCoequalizers
import EndKan.End.Core
import EndKan.Coend.Core

namespace EndKan.Kan

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Left Kan extension along K : C ⥤ D of F : C ⥤ E
    Lan_K F(d) = ∫^c Hom_D(K(c), d) × F(c) -/
def Lan (K : C ⥤ D) (F : C ⥤ E) [HasCoproductsOfShape C E] [HasWideCoequalizers E] : D ⥤ E where
  obj d := CoendObj (fun c => (K.obj c ⟶ d) × F.obj c)
  map f := Coend.map {
    app := fun c => (𝟙 (K.obj c ⟶ _)) × (𝟙 (F.obj c))
    dinaturality := by
      intro c c' g
      simp only [Category.assoc, Functor.map_comp, Category.comp_id, Category.id_comp]
      rw [← Category.assoc, ← Functor.map_comp]
      congr 1
      simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
  }
  map_id := by
    ext d
    apply Coend.uniq
    intro c
    simp only [Category.assoc, Coend.desc_ι, Category.id_comp]
  map_comp := by
    intro d d' d'' f g
    apply Coend.uniq
    intro c
    simp only [Category.assoc, Coend.desc_ι, Functor.map_comp]

/-- Right Kan extension along K : C ⥤ D of F : C ⥤ E
    Ran_K F(d) = ∫_c Hom_D(d, K(c)) → F(c) -/
def Ran (K : C ⥤ D) (F : C ⥤ E) [HasProductsOfShape C E] [HasWideEqualizers E] : D ⥤ E where
  obj d := EndObj (fun c => (d ⟶ K.obj c) → F.obj c)
  map f := End.map {
    app := fun c => (f ≫ 𝟙 (K.obj c)) → (𝟙 (F.obj c))
    dinaturality := by
      intro c c' g
      simp only [Category.assoc, Functor.map_comp, Category.comp_id, Category.id_comp]
      rw [← Category.assoc, ← Functor.map_comp]
      congr 1
      simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
  }
  map_id := by
    ext d
    apply End.uniq
    intro c
    simp only [Category.assoc, End.lift_π, Category.id_comp]
  map_comp := by
    intro d d' d'' f g
    apply End.uniq
    intro c
    simp only [Category.assoc, End.lift_π, Functor.map_comp]

/-- Universal property of left Kan extensions -/
def Lan.universal {K : C ⥤ D} {F : C ⥤ E} {G : D ⥤ E}
    [HasCoproductsOfShape C E] [HasWideCoequalizers E]
    (α : F ⟶ K ⋙ G) : Lan K F ⟶ G where
  app d := Coend.desc {
    app := fun c => α.app c
    dinaturality := by
      intro c c' f
      simp only [Category.assoc, α.naturality]
      rw [← Category.assoc, ← Functor.map_comp]
      congr 1
      simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
  }
  naturality := by
    intro d d' f
    apply Coend.uniq
    intro c
    simp only [Category.assoc, Coend.desc_ι, Functor.map_comp]

/-- Universal property of right Kan extensions -/
def Ran.universal {K : C ⥤ D} {F : C ⥤ E} {G : D ⥤ E}
    [HasProductsOfShape C E] [HasWideEqualizers E]
    (α : K ⋙ G ⟶ F) : G ⟶ Ran K F where
  app d := End.lift {
    app := fun c => α.app c
    dinaturality := by
      intro c c' f
      simp only [Category.assoc, α.naturality]
      rw [← Category.assoc, ← Functor.map_comp]
      congr 1
      simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
  }
  naturality := by
    intro d d' f
    apply End.uniq
    intro c
    simp only [Category.assoc, End.lift_π, Functor.map_comp]

/-- Left Kan extension preserves colimits -/
def Lan.preservesColimits (K : C ⥤ D) (F : C ⥤ E) [HasCoproductsOfShape C E] [HasWideCoequalizers E] :
  PreservesColimits (Lan K F) :=
  { preservesColimitsOfShape := fun J _ =>
    { preservesColimit := fun F' =>
      { preserves := fun c hc =>
        { fac := by simp
          uniq := by simp } } } }

/-- Right Kan extension preserves limits -/
def Ran.preservesLimits (K : C ⥤ D) (F : C ⥤ E) [HasProductsOfShape C E] [HasWideEqualizers E] :
  PreservesLimits (Ran K F) :=
  { preservesLimitsOfShape := fun J _ =>
    { preservesLimit := fun F' =>
      { preserves := fun c hc =>
        { fac := by simp
          uniq := by simp } } } }

/-- Left Kan extension along fully faithful functors -/
def Lan.fullyFaithful {K : C ⥤ D} (hK : Full K) (hK' : Faithful K) (F : C ⥤ E)
    [HasCoproductsOfShape C E] [HasWideCoequalizers E] :
    Lan K F ≅ F :=
  { hom := Lan.universal (𝟙 F)
    inv := Lan.universal (𝟙 F)
    hom_inv_id := by simp
    inv_hom_id := by simp }

/-- Right Kan extension along fully faithful functors -/
def Ran.fullyFaithful {K : C ⥤ D} (hK : Full K) (hK' : Faithful K) (F : C ⥤ E)
    [HasProductsOfShape C E] [HasWideEqualizers E] :
    Ran K F ≅ F :=
  { hom := Ran.universal (𝟙 F)
    inv := Ran.universal (𝟙 F)
    hom_inv_id := by simp
    inv_hom_id := by simp }

/-- Left Kan extension along identity -/
def Lan.id (F : C ⥤ E) [HasCoproductsOfShape C E] [HasWideCoequalizers E] :
  Lan (𝟙 C) F ≅ F :=
  { hom := Lan.universal (𝟙 F)
    inv := Lan.universal (𝟙 F)
    hom_inv_id := by simp
    inv_hom_id := by simp }

/-- Right Kan extension along identity -/
def Ran.id (F : C ⥤ E) [HasProductsOfShape C E] [HasWideEqualizers E] :
  Ran (𝟙 C) F ≅ F :=
  { hom := Ran.universal (𝟙 F)
    inv := Ran.universal (𝟙 F)
    hom_inv_id := by simp
    inv_hom_id := by simp }

/-- Left Kan extension along composition -/
def Lan.comp {K : C ⥤ D} {L : D ⥤ E} (F : C ⥤ E)
    [HasCoproductsOfShape C E] [HasWideCoequalizers E] :
    Lan (K ⋙ L) F ≅ Lan L (Lan K F) :=
  { hom := Lan.universal (Lan.universal (𝟙 F))
    inv := Lan.universal (Lan.universal (𝟙 F))
    hom_inv_id := by simp
    inv_hom_id := by simp }

/-- Right Kan extension along composition -/
def Ran.comp {K : C ⥤ D} {L : D ⥤ E} (F : C ⥤ E)
    [HasProductsOfShape C E] [HasWideEqualizers E] :
    Ran (K ⋙ L) F ≅ Ran L (Ran K F) :=
  { hom := Ran.universal (Ran.universal (𝟙 F))
    inv := Ran.universal (Ran.universal (𝟙 F))
    hom_inv_id := by simp
    inv_hom_id := by simp }

end EndKan.Kan
