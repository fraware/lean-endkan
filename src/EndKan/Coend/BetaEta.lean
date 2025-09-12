import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.Tactic.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import EndKan.Coend.Core

namespace EndKan.Coend

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- β-reduction for coends: composing through Coend.ι with F.map simplifies -/
theorem coend_beta {F : C × Cᵒᵖ ⥤ D} {X : D} (f : ∀ c : C, F.obj (c, op c) ⟶ X)
    (h : ∀ {c c' : C} (g : c ⟶ c'), F.map (g, op g) ≫ f c' = f c) (c : C) :
    Coend.ι F c ≫ Coend.desc f h = f c :=
  Coend.desc_ι f h c

/-- η-expansion for coends: uniqueness of mediating morphism -/
theorem coend_eta {F : C × Cᵒᵖ ⥤ D} {X : D} (f : CoendObj F ⟶ X) :
    f = Coend.desc (fun c => Coend.ι F c ≫ f) (by
      intro c c' g
      simp only [Category.assoc, Coend.ι_natural]) := by
  symm
  apply Coend.uniq
  intro c
  simp only [Category.assoc, Coend.desc_ι]

/-- β-reduction for coend inclusions -/
theorem coend_ι_beta {F : C × Cᵒᵖ ⥤ D} {c c' : C} (f : c ⟶ c') :
    F.map (f, op f) ≫ Coend.ι F c' = Coend.ι F c :=
  Coend.ι_natural F f

/-- η-expansion for coend inclusions -/
theorem coend_ι_eta {F : C × Cᵒᵖ ⥤ D} (c : C) :
    Coend.ι F c = Coend.ι F c := rfl

/-- β-reduction for coend maps -/
theorem coend_map_beta {F G : C × Cᵒᵖ ⥤ D} (α : F ⟶ G) (c : C) :
    Coend.ι F c ≫ Coend.map α = α.app (c, op c) ≫ Coend.ι G c :=
  Coend.map_ι α c

/-- η-expansion for coend maps -/
theorem coend_map_eta {F G : C × Cᵒᵖ ⥤ D} (α : F ⟶ G) :
    α = Coend.desc (fun c => α.app (c, op c) ≫ Coend.ι G c) (by
      intro c c' f
      simp only [Category.assoc, α.naturality, Coend.ι_natural]) := by
  symm
  apply Coend.uniq
  intro c
  simp only [Category.assoc, Coend.desc_ι]

/-- Composition of coend maps -/
theorem coend_map_comp {F G H : C × Cᵒᵖ ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    Coend.map α ≫ Coend.map β = Coend.map (α ≫ β) := by
  apply Coend.uniq
  intro c
  simp only [Category.assoc, Coend.map_ι, Coend.desc_ι]
  rw [← Category.assoc, Coend.map_ι, Category.assoc, Coend.map_ι]

/-- Identity coend map -/
theorem coend_map_id (F : C × Cᵒᵖ ⥤ D) :
    Coend.map (𝟙 F) = 𝟙 (CoendObj F) := by
  apply Coend.uniq
  intro c
  simp only [Category.assoc, Coend.map_ι, Category.comp_id, Category.id_comp]

/-- Coend map of natural transformation composition -/
theorem coend_map_whisker {F G : C × Cᵒᵖ ⥤ D} (α : F ⟶ G) (H : D ⥤ E) :
    Coend.map (α ▷ H) = H.map (Coend.ι F _) ≫ Coend.map α := by
  apply Coend.uniq
  intro c
  simp only [Category.assoc, Coend.map_ι, Functor.map_comp, Coend.desc_ι]

/-- Coend map of functor composition -/
theorem coend_map_hom {F G : C × Cᵒᵖ ⥤ D} (α : F ⟶ G) (H : E ⥤ D) :
    Coend.map (H.map α) = H.map (Coend.map α) := by
  apply Coend.uniq
  intro c
  simp only [Category.assoc, Coend.map_ι, Functor.map_comp, Coend.desc_ι]

/-- Coend of functor composition -/
theorem coend_comp {F : C × Cᵒᵖ ⥤ D} (H : D ⥤ E) :
    CoendObj (F ⋙ H) ≅ H.obj (CoendObj F) :=
  { hom := Coend.desc (fun c => H.map (Coend.ι F c)) (by
      intro c c' f
      simp only [Functor.map_comp, Coend.ι_natural])
    inv := H.map (Coend.desc (fun c => Coend.ι F c) (by simp))
    hom_inv_id := by
      apply Coend.uniq
      intro c
      simp only [Category.assoc, Coend.desc_ι, Functor.map_comp, Coend.desc_ι]
    inv_hom_id := by
      simp only [Functor.map_comp, Category.assoc, Coend.desc_ι, Functor.map_id, Category.comp_id] }

/-- Coend of opposite functor -/
theorem coend_op {F : C × Cᵒᵖ ⥤ D} :
    CoendObj (F.op) ≅ (CoendObj F).op :=
  { hom := (Coend.desc (fun c => (Coend.ι F c).op) (by
      intro c c' f
      simp only [← op_comp, Coend.ι_natural]))
    inv := (Coend.desc (fun c => (Coend.ι F c).unop) (by
      intro c c' f
      simp only [← unop_comp, Coend.ι_natural]))
    hom_inv_id := by
      simp only [← op_comp, Coend.desc_ι, op_unop, Category.comp_id]
    inv_hom_id := by
      simp only [← unop_comp, Coend.desc_ι, unop_op, Category.comp_id] }

/-- Coend of coproduct functor -/
theorem coend_coprod {F G : C × Cᵒᵖ ⥤ D} [HasBinaryCoproducts D] :
    CoendObj (F.coprod G) ≅ CoendObj F ⨿ CoendObj G :=
  { hom := Coend.desc (fun c => Coend.ι F c ⨿ Coend.ι G c) (by
      intro c c' f
      simp only [← Category.assoc, ← Coprod.comp_inl, ← Coprod.comp_inr, Coend.ι_natural])
    inv := Coprod.desc (Coend.desc (fun c => (Coend.ι (F.coprod G) c).inl) (by
        intro c c' f
        simp only [← Category.assoc, ← Coprod.comp_inl, Coend.ι_natural]))
      (Coend.desc (fun c => (Coend.ι (F.coprod G) c).inr) (by
        intro c c' f
        simp only [← Category.assoc, ← Coprod.comp_inr, Coend.ι_natural]))
    hom_inv_id := by
      apply Coend.uniq
      intro c
      simp only [Category.assoc, Coend.desc_ι, Coprod.desc_inl, Coprod.desc_inr]
    inv_hom_id := by
      simp only [← Coprod.comp_inl, ← Coprod.comp_inr, Coend.desc_ι, Coprod.desc_inl, Coprod.desc_inr] }

end EndKan.Coend
