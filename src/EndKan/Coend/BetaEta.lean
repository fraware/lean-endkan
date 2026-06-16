import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Opposites
import EndKan.Coend.Core

namespace EndKan.Coend

open CategoryTheory
open Opposite
open scoped Prod

variable {C : Type u} [Category.{v} C] {E : Type u} [Category.{v} E]

/-- β-reduction for coends: composing through `ι` with the universal morphism simplifies. -/
theorem coend_beta {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)] {X : E}
    (f : ∀ c : C, F.obj (c, op c) ⟶ X)
    (h : ∀ {c c' : C} (g : c ⟶ c'),
      F.map (𝟙 c ×ₘ g.op) ≫ f c = F.map (g ×ₘ 𝟙 (op c')) ≫ f c')
    (c : C) :
    ι F c ≫ desc (DinaturalTransformation.ofDiagonal f h) = f c := by
  rw [desc_ι, DinaturalTransformation.ofDiagonal, eqToHom_symm_comp_mpr_diagonal]

/-- η-expansion for coends: uniqueness of the mediating morphism. -/
theorem coend_eta {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)] {X : E}
    (f : CoendObj F ⟶ X) :
    f = desc {
      app := fun c => ιCurry F c ≫ f
      dinaturality := by
        intro c c' g
        rw [← Category.assoc, ιCurry_natural (F := F) g, Category.assoc] } := by
  symm
  apply uniq
  intro c
  rw [desc_ιCurry]

@[reassoc (attr := simp)]
theorem coend_ιCurry_beta {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)] {c c' : C} (f : c ⟶ c') :
    ((coendBifunctor F).map f.op).app c ≫ ιCurry F c =
      ((coendBifunctor F).obj (op c')).map f ≫ ιCurry F c' :=
  ιCurry_natural (F := F) f

/-- Diagonal coend injection dinaturality (`F.map` form). -/
@[reassoc (attr := simp)]
theorem coend_ι_beta {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)] {c c' : C} (f : c ⟶ c') :
    F.map (𝟙 c ×ₘ f.op) ≫ ι F c = F.map (f ×ₘ 𝟙 (op c')) ≫ ι F c' :=
  ι_dinatural (F := F) f

theorem coend_ι_eta {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)] (c : C) :
    ι F c = ι F c := rfl

@[reassoc (attr := simp)]
theorem coend_map_ιCurry {F G : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)]
    [Limits.HasCoend (coendBifunctor G)] (α : F ⟶ G) (c : C) :
    ιCurry F c ≫ map α =
      ((coendNatTrans α).app (op c)).app c ≫ ιCurry G c :=
  map_ιCurry α c

theorem coend_map_id {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)] :
    map (𝟙 F) = 𝟙 (CoendObj F) := by
  dsimp [map, CoendObj, coendBifunctor]
  exact Limits.coend.map_id (F := coendBifunctor F)

end EndKan.Coend
