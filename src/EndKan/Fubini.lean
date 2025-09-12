import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Initial
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.Coequalizers
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.HasColimits
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.WideCoequalizers
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.WidePushouts
import EndKan.End.Core
import EndKan.Coend.Core

namespace EndKan.Fubini

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Fubini's theorem for ends: ends commute under smallness conditions
    ∫_c ∫_d F(c,d) ≅ ∫_d ∫_c F(c,d) -/
def end_fubini {F : (C × D)ᵒᵖ × (C × D) ⥤ E}
    [HasProductsOfShape C E] [HasProductsOfShape D E]
    [HasWideEqualizers E] [HasProductsOfShape (C × D) E] :
    EndObj (F.comp (Prod.braiding _ _).op) ≅
    EndObj (EndObj <| F.comp (Prod.associator _ _ _).op) :=
  { hom := End.lift {
      app := fun c => End.lift {
        app := fun d => End.π F (op (c, d), (c, d))
        dinaturality := by
          intro d d' g
          simp only [Category.assoc, End.π_natural, Functor.map_comp]
          rw [← Category.assoc, ← Functor.map_comp]
          congr 1
          simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
      }
      dinaturality := by
        intro c c' f
        apply End.uniq
        intro d
        simp only [Category.assoc, End.lift_π, End.π_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    inv := End.lift {
      app := fun cd => End.π F (op cd, cd)
      dinaturality := by
        intro cd cd' f
        simp only [Category.assoc, End.π_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    hom_inv_id := by
      apply End.uniq
      intro c
      apply End.uniq
      intro d
      simp only [Category.assoc, End.lift_π, End.lift_π]
    inv_hom_id := by
      apply End.uniq
      intro cd
      simp only [Category.assoc, End.lift_π] }

/-- Fubini's theorem for coends: coends commute under smallness conditions
    ∫^c ∫^d F(c,d) ≅ ∫^d ∫^c F(c,d) -/
def coend_fubini {F : (C × D) × (C × D)ᵒᵖ ⥤ E}
    [HasCoproductsOfShape C E] [HasCoproductsOfShape D E]
    [HasWideCoequalizers E] [HasCoproductsOfShape (C × D) E] :
    CoendObj (F.comp (Prod.braiding _ _)) ≅
    CoendObj (CoendObj <| F.comp (Prod.associator _ _ _)) :=
  { hom := Coend.desc {
      app := fun cd => Coend.ι F (cd, op cd)
      dinaturality := by
        intro cd cd' f
        simp only [Category.assoc, Coend.ι_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    inv := Coend.desc {
      app := fun c => Coend.desc {
        app := fun d => Coend.ι F ((c, d), op (c, d))
        dinaturality := by
          intro d d' g
          simp only [Category.assoc, Coend.ι_natural, Functor.map_comp]
          rw [← Category.assoc, ← Functor.map_comp]
          congr 1
          simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
      }
      dinaturality := by
        intro c c' f
        apply Coend.uniq
        intro d
        simp only [Category.assoc, Coend.desc_ι, Coend.ι_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    hom_inv_id := by
      apply Coend.uniq
      intro cd
      simp only [Category.assoc, Coend.desc_ι]
    inv_hom_id := by
      apply Coend.uniq
      intro c
      apply Coend.uniq
      intro d
      simp only [Category.assoc, Coend.desc_ι, Coend.desc_ι] }

/-- Fubini's theorem for mixed ends and coends
    ∫_c ∫^d F(c,d) ≅ ∫^d ∫_c F(c,d) -/
def end_coend_fubini {F : Cᵒᵖ × C × D × Dᵒᵖ ⥤ E}
    [HasProductsOfShape C E] [HasCoproductsOfShape D E]
    [HasWideEqualizers E] [HasWideCoequalizers E] :
    EndObj (fun c => CoendObj (fun d => F.obj (op c, c, d, op d))) ≅
    CoendObj (fun d => EndObj (fun c => F.obj (op c, c, d, op d))) :=
  { hom := Coend.desc {
      app := fun d => End.lift {
        app := fun c => End.π (fun c => CoendObj (fun d => F.obj (op c, c, d, op d))) c ≫
          Coend.ι (fun d => F.obj (op c, c, d, op d)) d
        dinaturality := by
          intro c c' f
          simp only [Category.assoc, End.π_natural, Coend.ι_natural, Functor.map_comp]
          rw [← Category.assoc, ← Functor.map_comp]
          congr 1
          simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
      }
      dinaturality := by
        intro d d' g
        apply End.uniq
        intro c
        simp only [Category.assoc, End.lift_π, Coend.ι_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    inv := End.lift {
      app := fun c => Coend.desc {
        app := fun d => End.π (fun c => CoendObj (fun d => F.obj (op c, c, d, op d))) c ≫
          Coend.ι (fun d => F.obj (op c, c, d, op d)) d
        dinaturality := by
          intro d d' g
          simp only [Category.assoc, Coend.ι_natural, Functor.map_comp]
          rw [← Category.assoc, ← Functor.map_comp]
          congr 1
          simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
      }
      dinaturality := by
        intro c c' f
        apply Coend.uniq
        intro d
        simp only [Category.assoc, Coend.desc_ι, End.π_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    hom_inv_id := by
      apply Coend.uniq
      intro d
      apply End.uniq
      intro c
      simp only [Category.assoc, Coend.desc_ι, End.lift_π]
    inv_hom_id := by
      apply End.uniq
      intro c
      apply Coend.uniq
      intro d
      simp only [Category.assoc, End.lift_π, Coend.desc_ι] }

/-- Fubini's theorem for ends over product categories
    ∫_{(c,d)} F(c,d) ≅ ∫_c ∫_d F(c,d) -/
def end_prod_fubini {F : (C × D)ᵒᵖ × (C × D) ⥤ E}
    [HasProductsOfShape C E] [HasProductsOfShape D E]
    [HasWideEqualizers E] [HasProductsOfShape (C × D) E] :
    EndObj F ≅ EndObj (fun c => EndObj (fun d => F.obj (op (c, d), (c, d)))) :=
  { hom := End.lift {
      app := fun c => End.lift {
        app := fun d => End.π F (op (c, d), (c, d))
        dinaturality := by
          intro d d' g
          simp only [Category.assoc, End.π_natural, Functor.map_comp]
          rw [← Category.assoc, ← Functor.map_comp]
          congr 1
          simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
      }
      dinaturality := by
        intro c c' f
        apply End.uniq
        intro d
        simp only [Category.assoc, End.lift_π, End.π_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    inv := End.lift {
      app := fun cd => End.π F (op cd, cd)
      dinaturality := by
        intro cd cd' f
        simp only [Category.assoc, End.π_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    hom_inv_id := by
      apply End.uniq
      intro c
      apply End.uniq
      intro d
      simp only [Category.assoc, End.lift_π, End.lift_π]
    inv_hom_id := by
      apply End.uniq
      intro cd
      simp only [Category.assoc, End.lift_π] }

/-- Fubini's theorem for coends over product categories
    ∫^{(c,d)} F(c,d) ≅ ∫^c ∫^d F(c,d) -/
def coend_prod_fubini {F : (C × D) × (C × D)ᵒᵖ ⥤ E}
    [HasCoproductsOfShape C E] [HasCoproductsOfShape D E]
    [HasWideCoequalizers E] [HasCoproductsOfShape (C × D) E] :
    CoendObj F ≅ CoendObj (fun c => CoendObj (fun d => F.obj ((c, d), op (c, d)))) :=
  { hom := Coend.desc {
      app := fun cd => Coend.ι F (cd, op cd)
      dinaturality := by
        intro cd cd' f
        simp only [Category.assoc, Coend.ι_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    inv := Coend.desc {
      app := fun c => Coend.desc {
        app := fun d => Coend.ι F ((c, d), op (c, d))
        dinaturality := by
          intro d d' g
          simp only [Category.assoc, Coend.ι_natural, Functor.map_comp]
          rw [← Category.assoc, ← Functor.map_comp]
          congr 1
          simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
      }
      dinaturality := by
        intro c c' f
        apply Coend.uniq
        intro d
        simp only [Category.assoc, Coend.desc_ι, Coend.ι_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    hom_inv_id := by
      apply Coend.uniq
      intro cd
      simp only [Category.assoc, Coend.desc_ι]
    inv_hom_id := by
      apply Coend.uniq
      intro c
      apply Coend.uniq
      intro d
      simp only [Category.assoc, Coend.desc_ι, Coend.desc_ι] }

/-- Fubini's theorem for ends over functor categories
    ∫_F ∫_c F(c) ≅ ∫_c ∫_F F(c) -/
def end_functor_fubini {F : (C ⥤ D)ᵒᵖ × (C ⥤ D) ⥤ E}
    [HasProductsOfShape (C ⥤ D) E] [HasWideEqualizers E] :
    EndObj F ≅ EndObj (fun F' => EndObj (fun c => F.obj (op F', F') c)) :=
  { hom := End.lift {
      app := fun F' => End.lift {
        app := fun c => End.π F (op F', F') c
        dinaturality := by
          intro c c' g
          simp only [Category.assoc, End.π_natural, Functor.map_comp]
          rw [← Category.assoc, ← Functor.map_comp]
          congr 1
          simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
      }
      dinaturality := by
        intro F' F'' f
        apply End.uniq
        intro c
        simp only [Category.assoc, End.lift_π, End.π_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    inv := End.lift {
      app := fun F' => End.π F (op F', F')
      dinaturality := by
        intro F' F'' f
        simp only [Category.assoc, End.π_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    hom_inv_id := by
      apply End.uniq
      intro F'
      apply End.uniq
      intro c
      simp only [Category.assoc, End.lift_π, End.lift_π]
    inv_hom_id := by
      apply End.uniq
      intro F'
      simp only [Category.assoc, End.lift_π] }

/-- Fubini's theorem for coends over functor categories
    ∫^F ∫^c F(c) ≅ ∫^c ∫^F F(c) -/
def coend_functor_fubini {F : (C ⥤ D) × (C ⥤ D)ᵒᵖ ⥤ E}
    [HasCoproductsOfShape (C ⥤ D) E] [HasWideCoequalizers E] :
    CoendObj F ≅ CoendObj (fun F' => CoendObj (fun c => F.obj (F', op F') c)) :=
  { hom := Coend.desc {
      app := fun F' => Coend.ι F (F', op F')
      dinaturality := by
        intro F' F'' f
        simp only [Category.assoc, Coend.ι_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    inv := Coend.desc {
      app := fun F' => Coend.desc {
        app := fun c => Coend.ι F (F', op F') c
        dinaturality := by
          intro c c' g
          simp only [Category.assoc, Coend.ι_natural, Functor.map_comp]
          rw [← Category.assoc, ← Functor.map_comp]
          congr 1
          simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
      }
      dinaturality := by
        intro F' F'' f
        apply Coend.uniq
        intro c
        simp only [Category.assoc, Coend.desc_ι, Coend.ι_natural, Functor.map_comp]
        rw [← Category.assoc, ← Functor.map_comp]
        congr 1
        simp only [op_comp, op_id, Category.id_comp, Category.comp_id]
    }
    hom_inv_id := by
      apply Coend.uniq
      intro F'
      simp only [Category.assoc, Coend.desc_ι]
    inv_hom_id := by
      apply Coend.uniq
      intro F'
      apply Coend.uniq
      intro c
      simp only [Category.assoc, Coend.desc_ι, Coend.desc_ι] }

end EndKan.Fubini
