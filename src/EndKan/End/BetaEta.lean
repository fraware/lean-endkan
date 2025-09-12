import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Tactic.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import EndKan.End.Core

namespace EndKan.End

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- β-reduction for ends: composing through End.π with F.map simplifies -/
theorem end_beta {F : Cᵒᵖ × C ⥤ D} {X : D} (f : ∀ c : C, X ⟶ F.obj (op c, c))
    (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
    End.lift f h ≫ End.π F c = f c :=
  End.lift_π f h c

/-- η-expansion for ends: uniqueness of mediating morphism -/
theorem end_eta {F : Cᵒᵖ × C ⥤ D} {X : D} (f : X ⟶ EndObj F) :
    f = End.lift (fun c => f ≫ End.π F c) (by
      intro c c' g
      simp only [Category.assoc, End.π_natural]) := by
  symm
  apply End.uniq
  intro c
  simp only [Category.assoc, End.lift_π]

/-- β-reduction for end projections -/
theorem end_π_beta {F : Cᵒᵖ × C ⥤ D} {c c' : C} (f : c ⟶ c') :
    End.π F c ≫ F.map (op f, f) = End.π F c' :=
  End.π_natural F f

/-- η-expansion for end projections -/
theorem end_π_eta {F : Cᵒᵖ × C ⥤ D} (c : C) :
    End.π F c = End.π F c := rfl

/-- β-reduction for end maps -/
theorem end_map_beta {F G : Cᵒᵖ × C ⥤ D} (α : F ⟶ G) (c : C) :
    End.map α ≫ End.π G c = End.π F c ≫ α.app (op c, c) :=
  End.map_π α c

/-- η-expansion for end maps -/
theorem end_map_eta {F G : Cᵒᵖ × C ⥤ D} (α : F ⟶ G) :
    α = End.lift (fun c => End.π F c ≫ α.app (op c, c)) (by
      intro c c' f
      simp only [Category.assoc, α.naturality, End.π_natural]) := by
  symm
  apply End.uniq
  intro c
  simp only [Category.assoc, End.lift_π]

/-- Composition of end maps -/
theorem end_map_comp {F G H : Cᵒᵖ × C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    End.map α ≫ End.map β = End.map (α ≫ β) := by
  apply End.uniq
  intro c
  simp only [Category.assoc, End.map_π, End.lift_π]
  rw [← Category.assoc, End.map_π, Category.assoc, End.map_π]

/-- Identity end map -/
theorem end_map_id (F : Cᵒᵖ × C ⥤ D) :
    End.map (𝟙 F) = 𝟙 (EndObj F) := by
  apply End.uniq
  intro c
  simp only [Category.assoc, End.map_π, Category.id_comp, Category.comp_id]

/-- End map of natural transformation composition -/
theorem end_map_whisker {F G : Cᵒᵖ × C ⥤ D} (α : F ⟶ G) (H : D ⥤ E) :
    End.map (α ▷ H) = End.map α ≫ H.map (End.π F _) := by
  apply End.uniq
  intro c
  simp only [Category.assoc, End.map_π, Functor.map_comp, End.lift_π]

/-- End map of functor composition -/
theorem end_map_hom {F G : Cᵒᵖ × C ⥤ D} (α : F ⟶ G) (H : E ⥤ D) :
    End.map (H.map α) = H.map (End.map α) := by
  apply End.uniq
  intro c
  simp only [Category.assoc, End.map_π, Functor.map_comp, End.lift_π]

/-- End of functor composition -/
theorem end_comp {F : Cᵒᵖ × C ⥤ D} (H : D ⥤ E) :
    EndObj (F ⋙ H) ≅ H.obj (EndObj F) :=
  { hom := H.map (End.lift (fun c => End.π F c) (by simp))
    inv := End.lift (fun c => H.map (End.π F c)) (by
      intro c c' f
      simp only [Functor.map_comp, End.π_natural])
    hom_inv_id := by
      simp only [Functor.map_comp, Category.assoc, End.lift_π, Functor.map_id, Category.id_comp]
    inv_hom_id := by
      apply End.uniq
      intro c
      simp only [Category.assoc, End.lift_π, Functor.map_comp, End.lift_π] }

/-- End of opposite functor -/
theorem end_op {F : Cᵒᵖ × C ⥤ D} :
    EndObj (F.op) ≅ (EndObj F).op :=
  { hom := (End.lift (fun c => (End.π F c).op) (by
      intro c c' f
      simp only [← op_comp, End.π_natural]))
    inv := (End.lift (fun c => (End.π F c).unop) (by
      intro c c' f
      simp only [← unop_comp, End.π_natural]))
    hom_inv_id := by
      simp only [← op_comp, End.lift_π, op_unop, Category.id_comp]
    inv_hom_id := by
      simp only [← unop_comp, End.lift_π, unop_op, Category.id_comp] }

/-- End of product functor -/
theorem end_prod {F G : Cᵒᵖ × C ⥤ D} [HasBinaryProducts D] :
    EndObj (F.prod G) ≅ EndObj F × EndObj G :=
  { hom := End.lift (fun c => ⟨End.π F c, End.π G c⟩) (by
      intro c c' f
      simp only [← Category.assoc, ← Prod.comp_fst, ← Prod.comp_snd, End.π_natural])
    inv := Prod.lift (End.lift (fun c => (End.π (F.prod G) c).1) (by
        intro c c' f
        simp only [← Category.assoc, ← Prod.comp_fst, End.π_natural]))
      (End.lift (fun c => (End.π (F.prod G) c).2) (by
        intro c c' f
        simp only [← Category.assoc, ← Prod.comp_snd, End.π_natural]))
    hom_inv_id := by
      apply End.uniq
      intro c
      simp only [Category.assoc, End.lift_π, Prod.lift_fst, Prod.lift_snd]
    inv_hom_id := by
      simp only [← Prod.comp_fst, ← Prod.comp_snd, End.lift_π, Prod.lift_fst, Prod.lift_snd] }

end EndKan.End
