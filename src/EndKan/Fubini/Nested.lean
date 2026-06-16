import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Opposites
import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Fubini.Slice

namespace EndKan.Fubini

set_option linter.tacticCheckInstances false

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Prod
open Opposite
open scoped Prod

universe u v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

section nestedFubini

variable (F : EndIdx C D ⥤ E)
variable [AllEndSliceContrIso F]
variable [Limits.HasEnd (EndKan.End.endBifunctor F)]
variable [∀ d, Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
variable [∀ d, Epi (endInnerLift F d)]

/-- Outer profunctor for nested ends: at `(op d, d)` the fibre is the inner end over `C`. -/
noncomputable def endOuterProfunctor : Dᵒᵖ × D ⥤ E where
  obj p := endInnerObj F p.2
  map g := endInnerMap F g.2
  map_id := by
    intro p
    exact endInnerMap_id F p.2
  map_comp := by
    intro p p' p'' f g
    exact endInnerMap_comp F f.2 g.2

@[simp]
theorem endOuterProfunctor_map_prod {d d' : D} (f : d ⟶ d') :
    (endOuterProfunctor F).map (𝟙 (op d) ×ₘ f) = endInnerMap F f := rfl

@[simp]
theorem endOuterProfunctor_map_op {d d' : D} (f : d ⟶ d') :
    (endOuterProfunctor F).map (f.op ×ₘ 𝟙 d') = endInnerMap F (𝟙 d') := rfl

@[simp]
theorem endOuterProfunctor_obj (d : D) :
    (endOuterProfunctor F).obj (op d, d) = endInnerObj F d := rfl

@[simp]
theorem endOuterProfunctor_fiber_obj (d d' : D) :
    ((EndKan.End.endBifunctor (endOuterProfunctor F)).obj (op d)).obj d' =
      endInnerObj F d' := by
  rw [EndKan.End.endBifunctor_fiber_obj]
  rfl

@[simp]
theorem endOuterProfunctor_fiber_map {d d' : D} (f : d ⟶ d') :
    ((EndKan.End.endBifunctor (endOuterProfunctor F)).obj (op d)).map f =
      endInnerMap F f := by
  rw [EndKan.End.endBifunctor_obj_map, endOuterProfunctor_map_prod]

variable [Limits.HasEnd (EndKan.End.endBifunctor (endOuterProfunctor F))]

noncomputable abbrev endNestedObj : E :=
  EndKan.End.EndObj (endOuterProfunctor F)

noncomputable def endNestedπ (d : D) : endNestedObj F ⟶ endInnerObj F d :=
  EndKan.End.π (endOuterProfunctor F) d

noncomputable def endNestedπ_inner (cd : C × D) : endNestedObj F ⟶ F.obj (op cd, cd) :=
  endNestedπ F cd.2 ≫ endInnerπWedge F cd

noncomputable def endFubiniForward : EndKan.End.EndObj F ⟶ endNestedObj F :=
  EndKan.End.lift
    ⟨(fun d => endInnerLift F d), by
      intro d d' f
      simp only [EndKan.End.endBifunctor_obj_map, EndKan.End.endBifunctor_map_app,
        endOuterProfunctor_map_prod, endOuterProfunctor_map_op]
      calc
        endInnerLift F d ≫ endInnerMap F f = endInnerLift F d' := endInnerLift_natural F f
        _ = endInnerLift F d' ≫ endInnerMap F (𝟙 d') := by rw [endInnerMap_id, Category.comp_id]⟩

@[reassoc (attr := simp)]
theorem endFubiniForward_π (d : D) :
    endFubiniForward F ≫ endNestedπ F d = endInnerLift F d :=
  EndKan.End.lift_π _ d

theorem endFubiniForward_nested_inner (cd : C × D) :
    endFubiniForward F ≫ endNestedπ_inner F cd = EndKan.End.π F cd := by
  rw [endNestedπ_inner, ← Category.assoc, endFubiniForward_π, endInnerLift_πWedge]

theorem endNested_hom_ext {d : D} {f g : endNestedObj F ⟶ endInnerObj F d}
    (h : ∀ c : C, f ≫ endInnerπ F d c = g ≫ endInnerπ F d c) : f = g := by
  apply EndKan.End.uniq (F := endSlice F d)
  intro c
  rw [← endInnerπ_π F d c]
  exact h c

theorem endNestedπ_post_innerMap {d d' : D} (f : d ⟶ d') :
    endNestedπ F d ≫ endInnerMap F f =
      End.π (endOuterProfunctor F) d ≫
        ((EndKan.End.endBifunctor (endOuterProfunctor F)).obj (op d)).map f := by
  unfold endNestedπ
  rw [← endOuterProfunctor_fiber_map]
  rfl

theorem endNestedπ_id_innerMap (d : D) :
    endNestedπ F d ≫ endInnerMap F (𝟙 d) = endNestedπ F d := by
  apply endNested_hom_ext
  intro c
  rw [Category.assoc, endInnerMap_id, Category.id_comp]

theorem endNestedπ_endInnerMap {cd cd' : C × D} (fg : cd ⟶ cd') :
    endNestedπ F cd.2 ≫ endInnerMap F fg.2 = endNestedπ F cd'.2 := by
  refine Eq.trans (endNestedπ_post_innerMap F fg.2) ?_
  rw [EndKan.End.π_natural (F := endOuterProfunctor F) fg.2, EndKan.End.endBifunctor_map_app,
    endOuterProfunctor_map_op F fg.2, endNestedπ]
  exact endNestedπ_id_innerMap F cd'.2

theorem endNestedπ_inner_post_fmap {cd cd' : C × D} (fg : cd ⟶ cd') :
    (endNestedπ F cd.2 ≫ endInnerπWedge F cd) ≫ F.map (𝟙 (op cd) ×ₘ fg) =
      endNestedπ F cd'.2 ≫ endInnerπWedge F cd' ≫ F.map (fg.op ×ₘ 𝟙 cd') := by
  calc
    (endNestedπ F cd.2 ≫ endInnerπWedge F cd) ≫ F.map (𝟙 (op cd) ×ₘ fg)
        = endNestedπ F cd.2 ≫ (endInnerπWedge F cd ≫ F.map (𝟙 (op cd) ×ₘ fg)) := Category.assoc _ _ _
    _ = endNestedπ F cd.2 ≫ endInnerMap F fg.2 ≫ endInnerπWedge F cd' ≫ F.map (fg.op ×ₘ 𝟙 cd') := by
          rw [endInnerπWedge_dinatural F fg]
    _ = (endNestedπ F cd.2 ≫ endInnerMap F fg.2) ≫ endInnerπWedge F cd' ≫ F.map (fg.op ×ₘ 𝟙 cd') := by
          rw [← Category.assoc]
    _ = endNestedπ F cd'.2 ≫ endInnerπWedge F cd' ≫ F.map (fg.op ×ₘ 𝟙 cd') := by
          rw [← Category.assoc, endNestedπ_endInnerMap F fg]
          rw [← Category.assoc]

theorem endNestedπ_inner_dinatural {cd cd' : C × D} (fg : cd ⟶ cd') :
    endNestedπ_inner F cd ≫ ((EndKan.End.endBifunctor F).obj (op cd)).map fg =
      endNestedπ_inner F cd' ≫ ((EndKan.End.endBifunctor F).map fg.op).app cd' := by
  dsimp only [endNestedπ_inner]
  calc
    (endNestedπ F cd.2 ≫ endInnerπWedge F cd) ≫ ((EndKan.End.endBifunctor F).obj (op cd)).map fg
        = endNestedπ F cd.2 ≫ (endInnerπWedge F cd ≫
            ((EndKan.End.endBifunctor F).obj (op cd)).map fg) := Category.assoc _ _ _
    _ = endNestedπ F cd.2 ≫ endInnerMap F fg.2 ≫ endInnerπWedge F cd' ≫
          ((EndKan.End.endBifunctor F).map fg.op).app cd' := by
          rw [endInnerπWedge_dinatural_curry F fg]
    _ = (endNestedπ F cd'.2 ≫ endInnerπWedge F cd') ≫
          ((EndKan.End.endBifunctor F).map fg.op).app cd' := by
          rw [← Category.assoc, endNestedπ_endInnerMap F fg, Category.assoc]

noncomputable def endFubiniBackward : endNestedObj F ⟶ EndKan.End.EndObj F :=
  EndKan.End.lift
    ⟨(fun cd => endNestedπ_inner F cd), by
      intro cd cd' fg
      exact endNestedπ_inner_dinatural F fg⟩

@[reassoc (attr := simp)]
theorem endFubiniBackward_π (cd : C × D) :
    endFubiniBackward F ≫ EndKan.End.π F cd = endNestedπ_inner F cd :=
  EndKan.End.lift_π _ cd

noncomputable def endFubiniIso : EndKan.End.EndObj F ≅ endNestedObj F where
  hom := endFubiniForward F
  inv := endFubiniBackward F
  hom_inv_id := by
    apply EndKan.End.uniq (F := F)
    intro cd
    rw [Category.assoc, endFubiniBackward_π, endFubiniForward_nested_inner, Category.id_comp]
  inv_hom_id := by
    apply EndKan.End.uniq (F := endOuterProfunctor F)
    intro d
    have h : endFubiniBackward F ≫ endInnerLift F d = endNestedπ F d := by
      apply endNested_hom_ext
      intro c
      calc
        (endFubiniBackward F ≫ endInnerLift F d) ≫ endInnerπ F d c
            = endFubiniBackward F ≫ EndKan.End.π F (c, d) := by
              rw [Category.assoc, endInnerLift_π F d c]
        _ = endNestedπ_inner F (c, d) := endFubiniBackward_π F (c, d)
        _ = endNestedπ F d ≫ endInnerπ F d c := by
              dsimp only [endNestedπ_inner]
              congr 1
              exact (endInnerπWedge_π F c d).trans (endInnerπ_π F d c).symm
    calc
      (endFubiniBackward F ≫ endFubiniForward F) ≫ endNestedπ F d
          = endFubiniBackward F ≫ endInnerLift F d := by
            rw [Category.assoc, endFubiniForward_π]
      _ = endNestedπ F d := h
      _ = 𝟙 _ ≫ endNestedπ F d := by rw [Category.id_comp]

@[simp]
theorem endFubiniIso_hom : (endFubiniIso F).hom = endFubiniForward F := rfl

@[simp]
theorem endFubiniIso_inv : (endFubiniIso F).inv = endFubiniBackward F := rfl

end nestedFubini

end EndKan.Fubini
