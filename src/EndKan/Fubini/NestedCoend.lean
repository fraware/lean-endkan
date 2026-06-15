import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Opposites
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Fubini.CoendSlice

namespace EndKan.Fubini

set_option linter.tacticCheckInstances false

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Prod
open Opposite
open scoped Prod

universe u v

variable {C D E : Type u} [Category.{v, u} C] [Category.{v, u} D] [Category.{v, u} E]

section nestedCoendFubini

variable (F : (C × D) × (C × D)ᵒᵖ ⥤ E)
variable [CoendSliceContrIso F]
variable [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
variable [∀ d, Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
variable [∀ d, Mono (coendInnerDesc F d)]

/-- Outer profunctor for nested coends: at `(d, op d)` the fibre is the inner coend over `C`. -/
noncomputable def coendOuterProfunctor : D × Dᵒᵖ ⥤ E where
  obj p := coendInnerObj F p.1
  map g := coendInnerMap F g.1
  map_id := by
    intro p
    exact coendInnerMap_id F p.1
  map_comp := by
    intro p p' p'' f g
    exact coendInnerMap_comp F f.1 g.1

@[simp]
theorem coendOuterProfunctor_map_prod {d d' : D} (f : d ⟶ d') :
    (coendOuterProfunctor F).map (f ×ₘ 𝟙 (op d')) = coendInnerMap F f := rfl

@[simp]
theorem coendOuterProfunctor_map_fiber {d : D} {d' d'' : D} (f : d' ⟶ d'') :
    (coendOuterProfunctor F).map (f ×ₘ 𝟙 (op d)) = coendInnerMap F f := rfl

@[simp]
theorem coendOuterProfunctor_map_op {d d' : D} (f : d ⟶ d') :
    (coendOuterProfunctor F).map (𝟙 d ×ₘ f.op) = coendInnerMap F (𝟙 d) := rfl

@[simp]
theorem coendOuterProfunctor_obj (d : D) :
    (coendOuterProfunctor F).obj (d, op d) = coendInnerObj F d := rfl

@[simp]
theorem coendOuterProfunctor_fiber_obj (d d' : D) :
    ((EndKan.Coend.coendBifunctor (coendOuterProfunctor F)).obj (op d)).obj d' =
      coendInnerObj F d' := by
  rw [EndKan.Coend.coendDiagonal_app]
  rfl

theorem coendOuterProfunctor_fiber_map {d d' : D} (f : d ⟶ d') :
    ((EndKan.Coend.coendBifunctor (coendOuterProfunctor F)).obj (op d')).map f =
      coendInnerMap F f := by
  rw [EndKan.Coend.coendBifunctor_obj_map (F := coendOuterProfunctor F) (c := d) (c' := d'),
    coendOuterProfunctor_map_prod]

theorem coendOuterProfunctor_coendDiagonal (d : D) :
    ((EndKan.Coend.coendBifunctor (coendOuterProfunctor F)).obj (op d)).obj d = coendInnerObj F d :=
  (EndKan.Coend.coendDiagonal (F := coendOuterProfunctor F) d).trans (coendOuterProfunctor_obj F d)

variable [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendOuterProfunctor F))]

noncomputable abbrev coendNestedObj : E :=
  EndKan.Coend.CoendObj (coendOuterProfunctor F)

noncomputable def coendNestedι (d : D) : coendInnerObj F d ⟶ coendNestedObj F :=
  eqToHom (coendOuterProfunctor_obj F d).symm ≫ EndKan.Coend.ι (coendOuterProfunctor F) d

omit [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendOuterProfunctor F))] in
theorem coendOuterProfunctor_obj_eqToHom_symm (d : D) :
    eqToHom (coendOuterProfunctor_obj F d).symm ≫
      eqToHom (EndKan.Coend.coendDiagonal (F := coendOuterProfunctor F) d).symm =
    eqToHom (coendOuterProfunctor_coendDiagonal F d).symm :=
  eqToHom_trans (coendOuterProfunctor_obj F d).symm
    (EndKan.Coend.coendDiagonal (F := coendOuterProfunctor F) d).symm

theorem coendNestedι_eq_ιCurry (d : D) :
    coendNestedι F d =
      eqToHom (coendOuterProfunctor_coendDiagonal F d).symm ≫
        EndKan.Coend.ιCurry (coendOuterProfunctor F) d := by
  unfold coendNestedι
  rw [EndKan.Coend.ι_eq (F := coendOuterProfunctor F) d, ← coendOuterProfunctor_obj_eqToHom_symm F d,
    Category.assoc]

theorem coendNestedι_eq_ι (d : D) :
    coendNestedι F d = EndKan.Coend.ι (coendOuterProfunctor F) d := by
  unfold coendNestedι
  simp only [coendOuterProfunctor_obj, eqToHom_refl, Category.id_comp]

omit [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendOuterProfunctor F))] in
theorem coendInnerMap_eqToHom_obj {d d' : D} (f : d ⟶ d') :
    coendInnerMap F f ≫ eqToHom (coendOuterProfunctor_obj F d').symm =
    eqToHom (coendOuterProfunctor_obj F d).symm ≫
      ((EndKan.Coend.coendBifunctor (coendOuterProfunctor F)).obj (op d')).map f := by
  simp only [coendOuterProfunctor_obj, eqToHom_refl, coendOuterProfunctor_fiber_map, Category.comp_id,
    Category.id_comp]

noncomputable def coendNestedι_inner (cd : C × D) : F.obj (coendWedge cd.1 cd.2) ⟶ coendNestedObj F :=
  coendInnerιWedge F cd.2 cd.1 ≫ coendNestedι F cd.2

omit [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendOuterProfunctor F))] in
theorem coendInnerιWedge_dinatural {cd cd' : C × D} (fg : cd ⟶ cd') :
    F.map (fg ×ₘ 𝟙 (op cd')) ≫ coendInnerιWedge F cd'.2 cd'.1 =
      F.map (𝟙 cd ×ₘ fg.op) ≫ coendInnerιWedge F cd.2 cd.1 ≫ coendInnerMap F fg.2 := by
  apply (cancel_mono (coendInnerDesc F cd'.2)).mp
  rw [Category.assoc, Category.assoc, coendInnerDesc_ιWedge F cd'.2 cd'.1]
  rw [show EndKan.Coend.ι F (cd'.1, cd'.2) = EndKan.Coend.ι F cd' from rfl,
    ← EndKan.Coend.coend_ι_beta (F := F) fg]
  rw [← coendInnerDesc_ιWedge F cd.2 cd.1, ← Category.assoc, ← coendInnerDesc_natural F fg.2,
    Category.assoc, Category.assoc]

theorem coendInnerιWedge_dinatural_curry {cd cd' : C × D} (fg : cd ⟶ cd') :
    F.map (𝟙 cd ×ₘ fg.op) ≫ coendInnerιWedge F cd.2 cd.1 ≫ coendInnerMap F fg.2 =
      F.map (fg ×ₘ 𝟙 (op cd')) ≫ coendInnerιWedge F cd'.2 cd'.1 := by
  exact (coendInnerιWedge_dinatural F fg).symm

theorem coendNested_hom_ext {d : D} {f g : coendInnerObj F d ⟶ coendNestedObj F}
    (h : ∀ c : C, coendInnerι F d c ≫ f = coendInnerι F d c ≫ g) : f = g := by
  apply EndKan.Coend.uniq (F := coendSlice F d)
  intro c
  rw [coendInnerιCurry_eq F d c, Category.assoc, h c, ← Category.assoc, ← coendInnerιCurry_eq F d c]

theorem coendNestedι_post_innerMap {d d' : D} (f : d ⟶ d') :
    coendInnerMap F f ≫ coendNestedι F d' =
      ((EndKan.Coend.coendBifunctor (coendOuterProfunctor F)).map f.op).app d ≫ coendNestedι F d := by
  have h := (EndKan.Coend.ι_dinatural (F := coendOuterProfunctor F) f).symm
  rw [← EndKan.Coend.coendBifunctor_map_app, ← EndKan.Coend.coendBifunctor_obj_map] at h
  unfold coendNestedι
  simp only [Category.assoc, coendOuterProfunctor_obj, eqToHom_refl, Category.comp_id, Category.id_comp]
  exact h

theorem coendNestedι_id_innerMap (d : D) :
    coendInnerMap F (𝟙 d) ≫ coendNestedι F d = coendNestedι F d := by
  rw [coendNestedι_post_innerMap F (𝟙 d), EndKan.Coend.coendBifunctor_map_app,
    coendOuterProfunctor_map_op, coendInnerMap_id]
  exact Category.id_comp _

theorem coendNestedι_coendInnerMap {cd cd' : C × D} (fg : cd ⟶ cd') :
    coendInnerMap F fg.2 ≫ coendNestedι F cd'.2 = coendNestedι F cd.2 := by
  rw [coendNestedι_post_innerMap F fg.2]
  rw [EndKan.Coend.coendBifunctor_map_app, coendOuterProfunctor_map_op]
  exact coendNestedι_id_innerMap F cd.2

theorem coendNestedι_inner_post_fmap {cd cd' : C × D} (fg : cd ⟶ cd') :
    F.map (𝟙 cd ×ₘ fg.op) ≫ coendInnerιWedge F cd.2 cd.1 ≫ coendNestedι F cd.2 =
      F.map (fg ×ₘ 𝟙 (op cd')) ≫ coendInnerιWedge F cd'.2 cd'.1 ≫ coendNestedι F cd'.2 := by
  calc
    F.map (𝟙 cd ×ₘ fg.op) ≫ coendInnerιWedge F cd.2 cd.1 ≫ coendNestedι F cd.2
        = (F.map (𝟙 cd ×ₘ fg.op) ≫ coendInnerιWedge F cd.2 cd.1) ≫ coendNestedι F cd.2 :=
        (Category.assoc _ _ _).symm
    _ = F.map (𝟙 cd ×ₘ fg.op) ≫ (coendInnerιWedge F cd.2 cd.1 ≫ coendNestedι F cd.2) :=
        Category.assoc _ _ _
    _ = F.map (𝟙 cd ×ₘ fg.op) ≫ (coendInnerιWedge F cd.2 cd.1 ≫ coendInnerMap F fg.2 ≫
          coendNestedι F cd'.2) := by
          rw [← Category.assoc, coendNestedι_coendInnerMap F fg, Category.assoc]
    _ = (F.map (𝟙 cd ×ₘ fg.op) ≫ coendInnerιWedge F cd.2 cd.1 ≫ coendInnerMap F fg.2) ≫
          coendNestedι F cd'.2 := by
          rw [Category.assoc, Category.assoc]
    _ = (F.map (fg ×ₘ 𝟙 (op cd')) ≫ coendInnerιWedge F cd'.2 cd'.1) ≫ coendNestedι F cd'.2 :=
          congrArg (fun h => h ≫ coendNestedι F cd'.2) (coendInnerιWedge_dinatural_curry F fg)
    _ = F.map (fg ×ₘ 𝟙 (op cd')) ≫ coendInnerιWedge F cd'.2 cd'.1 ≫ coendNestedι F cd'.2 := by
          exact Category.assoc _ _ _

theorem coendNestedι_inner_dinatural {cd cd' : C × D} (fg : cd ⟶ cd') :
    F.map (𝟙 cd ×ₘ fg.op) ≫ coendNestedι_inner F cd =
      F.map (fg ×ₘ 𝟙 (op cd')) ≫ coendNestedι_inner F cd' := by
  dsimp only [coendNestedι_inner]
  exact coendNestedι_inner_post_fmap F fg

theorem coendFubiniBackward_dinatural {d d' : D} (f : d ⟶ d') :
    (coendOuterProfunctor F).map (𝟙 d ×ₘ f.op) ≫ coendInnerDesc F d =
      (coendOuterProfunctor F).map (f ×ₘ 𝟙 (op d')) ≫ coendInnerDesc F d' := by
  rw [coendOuterProfunctor_map_op, coendOuterProfunctor_map_prod]
  exact (coendInnerDesc_natural F (𝟙 d)).trans (coendInnerDesc_natural F f).symm

noncomputable def coendFubiniForward : EndKan.Coend.CoendObj F ⟶ coendNestedObj F :=
  EndKan.Coend.desc
    (EndKan.Coend.DinaturalTransformation.ofDiagonal
      (fun cd => coendNestedι_inner F cd)
      (by
        intro cd cd' fg
        exact coendNestedι_inner_dinatural F fg))

noncomputable def coendFubiniBackward : coendNestedObj F ⟶ EndKan.Coend.CoendObj F :=
  EndKan.Coend.desc
    (EndKan.Coend.DinaturalTransformation.ofDiagonal
      (fun d => coendInnerDesc F d)
      (by
        intro d d' f
        exact coendFubiniBackward_dinatural F f))

@[reassoc (attr := simp)]
theorem coendFubiniForward_ι (cd : C × D) :
    EndKan.Coend.ι F cd ≫ coendFubiniForward F = coendNestedι_inner F cd :=
  EndKan.Coend.coend_beta (F := F)
    (f := fun cd' => coendNestedι_inner F cd')
    (by
      intro cd' cd'' fg
      exact coendNestedι_inner_dinatural F fg) cd

@[reassoc (attr := simp)]
theorem coendFubiniBackward_ι (d : D) :
    coendNestedι F d ≫ coendFubiniBackward F = coendInnerDesc F d := by
  rw [coendNestedι_eq_ιCurry F d, show coendFubiniBackward F = EndKan.Coend.desc _ from rfl,
    Category.assoc, EndKan.Coend.desc_ιCurry, EndKan.Coend.DinaturalTransformation.ofDiagonal]
  exact EndKan.Coend.eqToHom_symm_comp_mpr_diagonal (F := coendOuterProfunctor F) (c := d)
    (f := coendInnerDesc F d)

theorem coendFubiniBackward_nested_inner (cd : C × D) :
    coendNestedι_inner F cd ≫ coendFubiniBackward F = EndKan.Coend.ι F cd := by
  rw [coendNestedι_inner, Category.assoc, coendFubiniBackward_ι, coendInnerDesc_ιWedge]

theorem coendFubiniForward_nestedι (d : D) :
    coendInnerDesc F d ≫ coendFubiniForward F = coendNestedι F d := by
  apply coendNested_hom_ext
  intro c
  calc
    coendInnerι F d c ≫ coendInnerDesc F d ≫ coendFubiniForward F
        = (coendInnerι F d c ≫ coendInnerDesc F d) ≫ coendFubiniForward F :=
        (Category.assoc _ _ _).symm
    _ = eqToHom (coendSlice_obj F d c) ≫ EndKan.Coend.ι F (c, d) ≫ coendFubiniForward F := by
          rw [coendInnerι_comp_desc F d c, Category.assoc]
    _ = eqToHom (coendSlice_obj F d c) ≫ coendNestedι_inner F (c, d) :=
          congrArg (fun h => eqToHom (coendSlice_obj F d c) ≫ h) (coendFubiniForward_ι F (c, d))
    _ = eqToHom (coendSlice_obj F d c) ≫ coendInnerιWedge F d c ≫ coendNestedι F d := rfl
    _ = coendInnerι F d c ≫ coendNestedι F d := by
          have h :
              eqToHom (coendSlice_obj F d c) ≫ coendInnerιWedge F d c = coendInnerι F d c := by
            rw [coendInnerιWedge_eq F d c]
            exact (eqToIso (coendSlice_obj F d c)).hom_inv_id_assoc (coendInnerι F d c)
          rw [← Category.assoc, h]

noncomputable def coendFubiniIso : EndKan.Coend.CoendObj F ≅ coendNestedObj F where
  hom := coendFubiniForward F
  inv := coendFubiniBackward F
  hom_inv_id := by
    apply EndKan.Coend.uniq (F := F)
    intro cd
    have hι : eqToHom (EndKan.Coend.coendDiagonal (F := F) cd) ≫ EndKan.Coend.ι F cd =
        EndKan.Coend.ιCurry F cd := by
      rw [EndKan.Coend.ι_eq (F := F) cd]
      have h₂ :
          eqToHom (EndKan.Coend.coendDiagonal (F := F) cd) ≫
              eqToHom (EndKan.Coend.coendDiagonal (F := F) cd).symm = 𝟙 _ := by
        simpa [eqToIso.inv, eqToIso.hom] using
          (eqToIso (EndKan.Coend.coendDiagonal (F := F) cd)).hom_inv_id
      rw [← Category.assoc, h₂, Category.id_comp]
    calc
      Coend.ιCurry F cd ≫ coendFubiniForward F ≫ coendFubiniBackward F
          = eqToHom (EndKan.Coend.coendDiagonal (F := F) cd) ≫ Coend.ι F cd ≫
              coendFubiniForward F ≫ coendFubiniBackward F := by
            rw [← hι, Category.assoc]
      _ = eqToHom (EndKan.Coend.coendDiagonal (F := F) cd) ≫
            (Coend.ι F cd ≫ coendFubiniForward F ≫ coendFubiniBackward F) := rfl
      _ = eqToHom (EndKan.Coend.coendDiagonal (F := F) cd) ≫ Coend.ι F cd := by
            have h :
                Coend.ι F cd ≫ coendFubiniForward F ≫ coendFubiniBackward F = Coend.ι F cd := by
              calc
                Coend.ι F cd ≫ coendFubiniForward F ≫ coendFubiniBackward F
                    = (Coend.ι F cd ≫ coendFubiniForward F) ≫ coendFubiniBackward F :=
                    (Category.assoc _ _ _).symm
                _ = coendNestedι_inner F cd ≫ coendFubiniBackward F := by rw [coendFubiniForward_ι F cd]
                _ = Coend.ι F cd := coendFubiniBackward_nested_inner F cd
            exact congrArg (fun f => eqToHom (EndKan.Coend.coendDiagonal (F := F) cd) ≫ f) h
      _ = Coend.ιCurry F cd ≫ 𝟙 _ := by rw [hι, Category.comp_id]
  inv_hom_id := by
    apply EndKan.Coend.uniq (F := coendOuterProfunctor F)
    intro d
    have hι : eqToHom (coendOuterProfunctor_coendDiagonal F d) ≫ coendNestedι F d =
        EndKan.Coend.ιCurry (coendOuterProfunctor F) d := by
      rw [coendNestedι_eq_ιCurry F d]
      exact (eqToIso (coendOuterProfunctor_coendDiagonal F d)).hom_inv_id_assoc
        (EndKan.Coend.ιCurry (coendOuterProfunctor F) d)
    calc
      Coend.ιCurry (coendOuterProfunctor F) d ≫ coendFubiniBackward F ≫ coendFubiniForward F
          = eqToHom (coendOuterProfunctor_coendDiagonal F d) ≫ coendNestedι F d ≫
              coendFubiniBackward F ≫ coendFubiniForward F := by
            rw [← hι, Category.assoc]
      _ = eqToHom (coendOuterProfunctor_coendDiagonal F d) ≫
            (coendNestedι F d ≫ coendFubiniBackward F ≫ coendFubiniForward F) := rfl
      _ = eqToHom (coendOuterProfunctor_coendDiagonal F d) ≫ coendNestedι F d := by
            have h :
                coendNestedι F d ≫ coendFubiniBackward F ≫ coendFubiniForward F = coendNestedι F d := by
              calc
                coendNestedι F d ≫ coendFubiniBackward F ≫ coendFubiniForward F
                    = (coendNestedι F d ≫ coendFubiniBackward F) ≫ coendFubiniForward F :=
                    (Category.assoc _ _ _).symm
                _ = coendInnerDesc F d ≫ coendFubiniForward F := by rw [coendFubiniBackward_ι F d]
                _ = coendNestedι F d := coendFubiniForward_nestedι F d
            exact congrArg (fun f => eqToHom (coendOuterProfunctor_coendDiagonal F d) ≫ f) h
      _ = Coend.ιCurry (coendOuterProfunctor F) d ≫ 𝟙 _ := by rw [hι, Category.comp_id]

@[simp]
theorem coendFubiniIso_hom : (coendFubiniIso F).hom = coendFubiniForward F := rfl

@[simp]
theorem coendFubiniIso_inv : (coendFubiniIso F).inv = coendFubiniBackward F := rfl

end nestedCoendFubini

end EndKan.Fubini
