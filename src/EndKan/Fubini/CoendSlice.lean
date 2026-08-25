import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.EqToHom
import EndKan.Coend.Core
import EndKan.Coend.BetaEta

namespace EndKan.Fubini

set_option linter.tacticCheckInstances false

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Prod
open Opposite
open scoped Prod

universe u v

variable {C D E : Type u} [Category.{v, u} C] [Category.{v, u} D] [Category.{v, u} E]

@[reducible] def coendWedge (c : C) (d : D) : (C × D) × (C × D)ᵒᵖ := ((c, d), op (c, d))

@[reducible] def coendOffCov (c : C) (d d' : D) : (C × D) × (C × D)ᵒᵖ := ((c, d'), op (c, d))

@[reducible] def coendMid (c : C) (d d' : D) : (C × D) × (C × D)ᵒᵖ := ((c, d), op (c, d'))

@[simp] theorem coendWedge_eq (c : C) (d : D) : coendWedge c d = ((c, d), op (c, d)) := rfl

@[simp] theorem coendOffCov_eq (c : C) (d d' : D) :
    coendOffCov c d d' = ((c, d'), op (c, d)) := rfl

@[simp] theorem coendMid_eq (c : C) (d d' : D) :
    coendMid c d d' = ((c, d), op (c, d')) := rfl

abbrev coendSliceEmbed (d : D) : C × Cᵒᵖ ⥤ (C × D) × (C × D)ᵒᵖ where
  obj pq := ((pq.1, d), op (pq.2.unop, d))
  map fg := ⟨fg.1 ×ₘ 𝟙 d, (fg.2.unop ×ₘ 𝟙 d).op⟩
  map_id := by
    intro pq
    apply Prod.hom_ext
    · simp [prod_id]
    · apply Quiver.Hom.unop_inj
      simp [prod_id, op_unop]
  map_comp := by
    intro pq pq' pq'' f g
    apply Prod.hom_ext
    · simp [prod_comp, Category.assoc]
    · apply Quiver.Hom.unop_inj
      simp [op_comp, prod_comp, Category.assoc, op_unop]

@[simp]
theorem coendSliceEmbed_obj (d : D) (c : C) :
    (coendSliceEmbed d).obj (c, op c) = coendWedge c d := by
  simp [coendSliceEmbed, coendWedge, op_unop]

abbrev coendSlice (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) : C × Cᵒᵖ ⥤ E :=
  coendSliceEmbed d ⋙ F

@[simp]
theorem coendSlice_as_comp (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) :
    coendSlice F d = coendSliceEmbed d ⋙ F := rfl

@[simp]
theorem coendSlice_obj (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C) :
    (coendSlice F d).obj (c, op c) = F.obj ((c, d), op (c, d)) := by
  simp [coendSlice, coendSliceEmbed, op_unop]

@[simp]
theorem coendSlice_obj_wedge (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C) :
    (coendSlice F d).obj (c, op c) = F.obj (coendWedge c d) := by
  simp [coendSlice_obj, coendWedge]

noncomputable abbrev coendInnerObj (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))] : E :=
  EndKan.Coend.CoendObj (coendSlice F d)

@[simp]
theorem coendInnerObj_eq (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))] :
    coendInnerObj F d = EndKan.Coend.CoendObj (coendSlice F d) := rfl

noncomputable def coendInnerι (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))] (c : C) :
    (coendSlice F d).obj (c, op c) ⟶ coendInnerObj F d :=
  EndKan.Coend.ι (coendSlice F d) c

noncomputable def coendInnerιWedge (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))] (c : C) :
    F.obj (coendWedge c d) ⟶ coendInnerObj F d :=
  eqToHom (coendSlice_obj F d c).symm ≫ coendInnerι F d c

@[simp]
theorem coendInnerιWedge_eq (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))] (c : C) :
    coendInnerιWedge F d c =
      eqToHom (coendSlice_obj F d c).symm ≫ coendInnerι F d c := rfl

noncomputable def coendInnerDesc (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendInnerObj F d ⟶ EndKan.Coend.CoendObj F :=
  EndKan.Coend.desc
    (EndKan.Coend.DinaturalTransformation.ofDiagonal
      (fun c => EndKan.Coend.ι F (c, d))
      (by
        intro c c' g
        exact EndKan.Coend.ι_dinatural (F := F) (f := g ×ₘ 𝟙 d)))

@[reassoc (attr := simp)]
theorem coendInnerDesc_ι (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] (c : C) :
    coendInnerι F d c ≫ coendInnerDesc F d = EndKan.Coend.ι F (c, d) := by
  show EndKan.Coend.ι (coendSlice F d) c ≫ coendInnerDesc F d = EndKan.Coend.ι F (c, d)
  exact EndKan.Coend.coend_beta (F := coendSlice F d) (f := fun c' => EndKan.Coend.ι F (c', d))
    (by
      intro c' c'' g
      exact EndKan.Coend.ι_dinatural (F := F) (f := g ×ₘ 𝟙 d)) c

theorem coendInnerDesc_ιWedge (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] (c : C) :
    coendInnerιWedge F d c ≫ coendInnerDesc F d = EndKan.Coend.ι F (c, d) := by
  have h₁ := coendInnerDesc_ι F d c
  have h₂ :=
    congrArg (fun g =>
      (congrArg (fun X => X ⟶ EndKan.Coend.CoendObj F) (coendSlice_obj F d c).symm).mpr g) h₁
  conv_lhs at h₂ =>
    rw [congrArg_mpr_hom_left]
    dsimp only [coendInnerιWedge]
    rw [← Category.assoc]
  exact h₂

@[reassoc]
theorem coendInnerDesc_ι_comp (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    {X : E} (f : X ⟶ (coendSlice F d).obj (c, op c))
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    (f ≫ coendInnerι F d c) ≫ coendInnerDesc F d = f ≫ EndKan.Coend.ι F (c, d) := by
  rw [Category.assoc, coendInnerDesc_ι F d c]

@[reassoc]
theorem coendInnerι_comp_desc (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendInnerι F d c ≫ coendInnerDesc F d =
      eqToHom (coendSlice_obj F d c) ≫ EndKan.Coend.ι F (c, d) := by
  rw [← (eqToIso (coendSlice_obj F d c)).hom_inv_id_assoc (coendInnerι F d c)]
  rw [eqToIso.hom, eqToIso.inv, Category.assoc, ← coendInnerιWedge_eq F d c,
    coendInnerDesc_ιWedge F d c]

@[reassoc]
theorem coendSlice_post_ι (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    {X : E} (f : X ⟶ (coendSlice F d).obj (c, op c))
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    (f ≫ coendInnerι F d c) ≫ coendInnerDesc F d =
      f ≫ eqToHom (coendSlice_obj F d c) ≫ EndKan.Coend.ι F (c, d) := by
  rw [Category.assoc, coendInnerι_comp_desc F d c]

section sliceMaps

variable (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')

noncomputable def coendSliceCov :
    F.obj ((c, d), op (c, d)) ⟶ F.obj ((c, d'), op (c, d)) :=
  F.map ((𝟙 c ×ₘ f), 𝟙 (op (c, d)))

noncomputable def coendSliceContr :
    F.obj ((c, d'), op (c, d')) ⟶ F.obj ((c, d'), op (c, d)) :=
  F.map (𝟙 (c, d'), (𝟙 c ×ₘ f).op)

noncomputable def coendSliceMidToWedge :
    F.obj ((c, d), op (c, d')) ⟶ F.obj ((c, d), op (c, d)) :=
  F.map (𝟙 (c, d), (𝟙 c ×ₘ f).op)

noncomputable def coendSliceMidTrans :
    F.obj ((c, d), op (c, d')) ⟶ F.obj ((c, d'), op (c, d')) :=
  F.map ((𝟙 c ×ₘ f), 𝟙 (op (c, d')))

@[reassoc (attr := simp)]
theorem coendSliceMid_comp :
    coendSliceMidToWedge F c d d' f ≫ coendSliceCov F c d d' f =
      coendSliceMidTrans F c d d' f ≫ coendSliceContr F c d d' f := by
  dsimp [coendSliceMidToWedge, coendSliceCov, coendSliceMidTrans, coendSliceContr]
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  apply Prod.hom_ext <;> simp [prod_comp, op_comp, op_unop]

@[reassoc (attr := simp)]
theorem coendSliceMid_ιCurry
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendSliceMidToWedge F c d d' f ≫ EndKan.Coend.ιCurry F (c, d) =
      coendSliceMidTrans F c d d' f ≫ EndKan.Coend.ιCurry F (c, d') := by
  dsimp [coendSliceMidToWedge, coendSliceMidTrans]
  exact EndKan.Coend.ιCurry_natural (F := F) (f := 𝟙 c ×ₘ f)

@[reassoc (attr := simp)]
theorem coendSliceMid_ι
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendSliceMidToWedge F c d d' f ≫ EndKan.Coend.ι F (c, d) =
      coendSliceMidTrans F c d d' f ≫ EndKan.Coend.ι F (c, d') := by
  dsimp [coendSliceMidToWedge, coendSliceMidTrans, coendMid, coendWedge]
  simpa using EndKan.Coend.ι_dinatural (F := F) (f := 𝟙 c ×ₘ f)

noncomputable def coendSliceOpCovIso [IsIso (coendSliceContr F c d d' f)] :
    F.obj (coendWedge c d) ⟶ F.obj (coendWedge c d') :=
  coendSliceCov F c d d' f ≫ CategoryTheory.inv (coendSliceContr F c d d' f)

theorem coendSliceOpCovIso_comp_contr [IsIso (coendSliceContr F c d d' f)] :
    coendSliceOpCovIso F c d d' f ≫ coendSliceContr F c d d' f =
      coendSliceCov F c d d' f := by
  simp [coendSliceOpCovIso, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem coendOffCov_wedge_ext [IsIso (coendSliceContr F c d d' f)]
    {u v : F.obj (coendOffCov c d d') ⟶ F.obj (coendWedge c d')}
    (_ : coendSliceCov F c d d' f ≫ u = coendSliceCov F c d d' f ≫ v)
    (h₂ : coendSliceContr F c d d' f ≫ u = coendSliceContr F c d d' f ≫ v) : u = v := by
  have h := congrArg (CategoryTheory.inv (coendSliceContr F c d d' f) ≫ ·) h₂
  simpa [Category.assoc, IsIso.inv_hom_id, Category.id_comp] using h

theorem coendOffCov_wedge_ext' (hContr : IsIso (coendSliceContr F c d d' f))
    {u v : F.obj (coendOffCov c d d') ⟶ F.obj (coendWedge c d')}
    (_ : coendSliceCov F c d d' f ≫ u = coendSliceCov F c d d' f ≫ v)
    (h₂ : coendSliceContr F c d d' f ≫ u = coendSliceContr F c d d' f ≫ v) : u = v := by
  have h := congrArg (fun x => @CategoryTheory.inv _ _ _ _ (coendSliceContr F c d d' f) hContr ≫ x) h₂
  have hu : @CategoryTheory.inv _ _ _ _ (coendSliceContr F c d d' f) hContr ≫
      coendSliceContr F c d d' f ≫ u = u := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hv : @CategoryTheory.inv _ _ _ _ (coendSliceContr F c d d' f) hContr ≫
      coendSliceContr F c d d' f ≫ v = v := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hu, hv] at h; exact h

noncomputable def coendSliceInvContr [IsIso (coendSliceCov F c d d' f)]
    [IsIso (coendSliceContr F c d d' f)] :
    F.obj (coendOffCov c d d') ⟶ F.obj (coendWedge c d') :=
  CategoryTheory.inv (coendSliceCov F c d d' f) ≫ coendSliceOpCovIso F c d d' f

theorem coendSliceInvContr_eq_invContr [IsIso (coendSliceCov F c d d' f)]
    [IsIso (coendSliceContr F c d d' f)] :
    coendSliceInvContr F c d d' f = CategoryTheory.inv (coendSliceContr F c d d' f) := by
  apply coendOffCov_wedge_ext (F := F) (c := c) (d := d) (d' := d') (f := f)
  · dsimp [coendSliceInvContr, coendSliceOpCovIso]
    rw [← Category.assoc, IsIso.hom_inv_id (coendSliceCov F c d d' f), Category.id_comp]
  · dsimp only [coendSliceInvContr, coendSliceOpCovIso]
    rw [← Category.assoc (CategoryTheory.inv (coendSliceCov F c d d' f)) (coendSliceCov F c d d' f)
        (CategoryTheory.inv (coendSliceContr F c d d' f)),
      IsIso.inv_hom_id (coendSliceCov F c d d' f), Category.id_comp]

theorem coendSliceContr_hom_inv [IsIso (coendSliceCov F c d d' f)] [IsIso (coendSliceContr F c d d' f)] :
    coendSliceContr F c d d' f ≫ coendSliceInvContr F c d d' f = 𝟙 (F.obj (coendWedge c d')) := by
  rw [coendSliceInvContr_eq_invContr, IsIso.hom_inv_id]

theorem coendSliceContr_inv_hom [IsIso (coendSliceCov F c d d' f)] [IsIso (coendSliceContr F c d d' f)] :
    coendSliceInvContr F c d d' f ≫ coendSliceContr F c d d' f = 𝟙 (F.obj (coendOffCov c d d')) := by
  dsimp only [coendSliceInvContr]
  rw [Category.assoc, coendSliceOpCovIso_comp_contr, IsIso.inv_hom_id]

theorem coendSliceOpCovIso_isIso [IsIso (coendSliceCov F c d d' f)] [IsIso (coendSliceContr F c d d' f)] :
    IsIso (coendSliceOpCovIso F c d d' f) := by
  simpa [coendSliceOpCovIso] using
    (inferInstance : IsIso (coendSliceCov F c d d' f ≫ CategoryTheory.inv (coendSliceContr F c d d' f)))

noncomputable def coendSliceCovInv [IsIso (coendSliceCov F c d d' f)] [IsIso (coendSliceContr F c d d' f)] :
    F.obj (coendOffCov c d d') ⟶ F.obj (coendWedge c d) :=
  coendSliceInvContr F c d d' f ≫
    @CategoryTheory.inv _ _ _ _ (coendSliceOpCovIso F c d d' f)
      (coendSliceOpCovIso_isIso F c d d' f)

theorem coendSliceCov_inv_hom [IsIso (coendSliceCov F c d d' f)] [IsIso (coendSliceContr F c d d' f)] :
    coendSliceCovInv F c d d' f ≫ coendSliceCov F c d d' f = 𝟙 (F.obj (coendOffCov c d d')) := by
  have hOpCov := coendSliceOpCovIso_isIso F c d d' f
  have hInvContr := (coendSliceInvContr_eq_invContr F c d d' f).symm
  dsimp only [coendSliceCovInv, coendSliceInvContr]
  have htail :
      @CategoryTheory.inv _ _ _ _ (coendSliceOpCovIso F c d d' f) hOpCov ≫ coendSliceCov F c d d' f =
        coendSliceContr F c d d' f := by
    rw [← coendSliceOpCovIso_comp_contr, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  simp only [Category.assoc, htail, coendSliceOpCovIso_comp_contr, IsIso.inv_hom_id]

theorem coendSliceCov_hom_inv [IsIso (coendSliceCov F c d d' f)] [IsIso (coendSliceContr F c d d' f)] :
    coendSliceCov F c d d' f ≫ coendSliceCovInv F c d d' f = 𝟙 (F.obj (coendWedge c d)) := by
  have hInvContr := (coendSliceInvContr_eq_invContr F c d d' f).symm
  dsimp only [coendSliceCovInv, coendSliceInvContr]
  simp only [Category.assoc, hInvContr, coendSliceOpCovIso, IsIso.hom_inv_id, Category.comp_id]

theorem coendSliceMid_opIso [IsIso (coendSliceContr F c d d' f)] :
    coendSliceMidToWedge F c d d' f ≫ coendSliceOpCovIso F c d d' f =
      coendSliceMidTrans F c d d' f := by
  dsimp [coendSliceOpCovIso]
  rw [← Category.assoc, coendSliceMid_comp F c d d' f, IsIso.comp_inv_eq]

noncomputable def coendSliceOpCovToSlice (c : C) {d d' : D} (f : d ⟶ d')
    [IsIso (coendSliceContr F c d d' f)] :
    (coendSlice F d).obj (c, op c) ⟶ (coendSlice F d').obj (c, op c) :=
  eqToHom (coendSlice_obj F d c) ≫
    coendSliceOpCovIso F c d d' f ≫
    eqToHom (coendSlice_obj F d' c).symm

theorem coendSliceOpCovToSlice_eq_opCovIso (c : C) {d d' : D} (f : d ⟶ d')
    [IsIso (coendSliceContr F c d d' f)] :
    coendSliceOpCovToSlice F c f =
      eqToHom (coendSlice_obj F d c) ≫
        coendSliceOpCovIso F c d d' f ≫
        eqToHom (coendSlice_obj F d' c).symm := rfl

end sliceMaps

section sliceIsoPackaging

variable (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')

@[reducible] noncomputable def coendSliceContrIsoFromData (hCov : IsIso (coendSliceCov F c d d' f))
    (hContr : IsIso (coendSliceContr F c d d' f)) :
    IsIso (coendSliceContr F c d d' f) := by
  letI := hCov
  letI := hContr
  exact IsIso.mk ⟨coendSliceInvContr F c d d' f, coendSliceContr_hom_inv F c d d' f,
    coendSliceContr_inv_hom F c d d' f⟩

@[reducible] noncomputable def coendSliceCovIsoFromData (hCov : IsIso (coendSliceCov F c d d' f))
    (hContr : IsIso (coendSliceContr F c d d' f)) :
    IsIso (coendSliceCov F c d d' f) := by
  letI := hCov
  letI := hContr
  exact IsIso.mk ⟨coendSliceCovInv F c d d' f, coendSliceCov_hom_inv F c d d' f,
    coendSliceCov_inv_hom F c d d' f⟩

end sliceIsoPackaging

/-- Joint separation for maps into `F.obj (coendOffCov c d d')`. -/
class CoendSliceJointMono (F : (C × D) × (C × D)ᵒᵖ ⥤ E) where
  ext :
    ∀ (c : C) (d d' : D) (f : d ⟶ d') {u v : F.obj (coendOffCov c d d') ⟶ F.obj (coendWedge c d')}
      (_ : coendSliceCov F c d d' f ≫ u = coendSliceCov F c d d' f ≫ v)
      (h₂ : coendSliceContr F c d d' f ≫ u = coendSliceContr F c d d' f ≫ v), u = v

section sliceIsoBootstrap

variable (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')

/-!
rc1 blocker (Attempt 4): seeded mutual `noncomputable def` cannot close (same as end side).

Joint-mono closure (Attempt 5): `[IsIso (coendSliceCov F c d d' f)]` + `[CoendSliceJointMono F]` does not
determine `[IsIso (coendSliceContr F c d d' f)]` for the same reasons as the end side (`coendSliceInvContr`,
`coendSliceContr_hom_inv`, `coendOffCov_wedge_ext'` all need bilateral leg isos). Consumer path:
`coendSliceContrIsoOfData` on concrete `F` (see `EndKan.Fubini.Examples`).
-/

end sliceIsoBootstrap

/-- Every contravariant slice leg for `F` is an isomorphism, and mid maps are epimorphisms
(supplied for nested Fubini). -/
class CoendSliceContrIso (F : (C × D) × (C × D)ᵒᵖ ⥤ E) where
  contrIso : ∀ (c : C) (d d' : D) (f : d ⟶ d'), IsIso (coendSliceContr F c d d' f)
  midEpi : ∀ (c : C) (d d' : D) (f : d ⟶ d'), Epi (coendSliceMidToWedge F c d d' f)

section sliceIsoJointMono

variable (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')
variable [CoendSliceJointMono F]

omit [CoendSliceJointMono F] in
theorem coendSliceContr_isIso_of_jointMono (hCov : IsIso (coendSliceCov F c d d' f))
    (hContr : IsIso (coendSliceContr F c d d' f)) :
    IsIso (coendSliceContr F c d d' f) :=
  coendSliceContrIsoFromData F c d d' f hCov hContr

@[reducible] def coendSliceContrIsoOfData {F : (C × D) × (C × D)ᵒᵖ ⥤ E}
    (h :
      ∀ (c : C) (d d' : D) (f : d ⟶ d'),
        IsIso (coendSliceCov F c d d' f) ∧ IsIso (coendSliceContr F c d d' f))
    (hMid :
      ∀ (c : C) (d d' : D) (f : d ⟶ d'), Epi (coendSliceMidToWedge F c d d' f)) :
    CoendSliceContrIso F where
  contrIso c d d' f := coendSliceContrIsoFromData F c d d' f (h c d d' f).1 (h c d d' f).2
  midEpi c d d' f := hMid c d d' f

/-- When cov legs are iso and joint separation holds, supply contr/mid data to close Fubini. -/
class CoendSliceIsoData (F : (C × D) × (C × D)ᵒᵖ ⥤ E) [CoendSliceJointMono F]
    extends CoendSliceContrIso F where
  covIso : ∀ (c : C) (d d' : D) (f : d ⟶ d'), IsIso (coendSliceCov F c d d' f)

end sliceIsoJointMono

noncomputable instance instCoendSliceContrIsIso {F : (C × D) × (C × D)ᵒᵖ ⥤ E} (c : C) (d d' : D)
    (f : d ⟶ d') [CoendSliceContrIso F] : IsIso (coendSliceContr F c d d' f) :=
  CoendSliceContrIso.contrIso (F := F) c d d' f

noncomputable instance instCoendSliceMidEpi {F : (C × D) × (C × D)ᵒᵖ ⥤ E} (c : C) (d d' : D)
    (f : d ⟶ d') [CoendSliceContrIso F] : Epi (coendSliceMidToWedge F c d d' f) :=
  CoendSliceContrIso.midEpi (F := F) c d d' f

section sliceIsoLemmas

variable (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')

@[reassoc (attr := simp)]
theorem coendSliceOpCovIso_post_ι [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendSliceOpCovIso F c d d' f ≫ EndKan.Coend.ι F (c, d') = EndKan.Coend.ι F (c, d) := by
  have h :
      coendSliceMidToWedge F c d d' f ≫ coendSliceOpCovIso F c d d' f ≫ EndKan.Coend.ι F (c, d') =
        coendSliceMidToWedge F c d d' f ≫ EndKan.Coend.ι F (c, d) := by
    rw [← Category.assoc, coendSliceMid_opIso F c d d' f, coendSliceMid_ι F c d d' f]
  exact (cancel_epi (coendSliceMidToWedge F c d d' f)).mp h

@[reassoc (attr := simp)]
theorem coendSliceOpCovIso_sec [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    EndKan.Coend.ι F (c, d) =
      coendSliceOpCovIso F c d d' f ≫ EndKan.Coend.ι F (c, d') := by
  exact (coendSliceOpCovIso_post_ι F c d d' f).symm

theorem eqToHom_symm_post_coendι (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    eqToHom (coendSlice_obj F d c).symm ≫ eqToHom (coendSlice_obj F d c) ≫
        EndKan.Coend.ι F (c, d) =
      EndKan.Coend.ι F (c, d) := by
  dsimp [eqToIso.inv, eqToIso.hom]
  exact (eqToIso (coendSlice_obj F d c)).inv_hom_id_assoc (EndKan.Coend.ι F (c, d))

@[reassoc (attr := simp)]
theorem coendSliceOpCovToSlice_post_ι [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendSliceOpCovToSlice F c f ≫ eqToHom (coendSlice_obj F d' c) ≫ EndKan.Coend.ι F (c, d') =
      eqToHom (coendSlice_obj F d c) ≫ EndKan.Coend.ι F (c, d) := by
  rw [coendSliceOpCovToSlice_eq_opCovIso F c f]
  refine (cancel_epi (eqToHom (coendSlice_obj F d c))).mp ?_
  rw [← Category.assoc, ← Category.assoc, ← coendSliceOpCovIso_post_ι F c d d' f]
  simp only [eqToIso.inv, eqToIso.hom, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.assoc]

@[reassoc]
theorem coendSliceOpCovToSlice_post_ι_wedge [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendSliceOpCovToSlice F c f ≫ eqToHom (coendSlice_obj F d' c) ≫ EndKan.Coend.ι F (c, d') =
      eqToHom (coendSlice_obj F d c) ≫ EndKan.Coend.ι F (c, d) :=
  coendSliceOpCovToSlice_post_ι F c d d' f

end sliceIsoLemmas

lemma eqToHom_coendDiagonal_slice (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))] :
    eqToHom (EndKan.Coend.coendDiagonal (F := coendSlice F d) c) ≫
        (eqToHom (EndKan.Coend.coendDiagonal (F := coendSlice F d) c).symm ≫
          EndKan.Coend.ιCurry (coendSlice F d) c) =
      EndKan.Coend.ιCurry (coendSlice F d) c := by
  rw [← Category.assoc, eqToHom_trans (EndKan.Coend.coendDiagonal (F := coendSlice F d) c),
    eqToHom_refl, Category.id_comp]

@[reassoc]
theorem coendInnerι_eq_ιCurry (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))] :
    coendInnerι F d c = eqToHom (EndKan.Coend.coendDiagonal (F := coendSlice F d) c).symm ≫
      EndKan.Coend.ιCurry (coendSlice F d) c :=
  EndKan.Coend.ι_eq (F := coendSlice F d) c

@[reassoc]
theorem coendInnerιCurry_eq (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))] :
    EndKan.Coend.ιCurry (coendSlice F d) c =
      eqToHom (EndKan.Coend.coendDiagonal (F := coendSlice F d) c) ≫ coendInnerι F d c := by
  symm
  rw [coendInnerι_eq_ιCurry F d c, ← Category.assoc]
  have h :
      eqToHom (EndKan.Coend.coendDiagonal (F := coendSlice F d) c) ≫
        eqToHom (EndKan.Coend.coendDiagonal (F := coendSlice F d) c).symm = 𝟙 _ := by
    simpa [eqToIso.inv, eqToIso.hom] using
      (eqToIso (EndKan.Coend.coendDiagonal (F := coendSlice F d) c)).hom_inv_id
  rw [h, Category.id_comp]


@[reassoc]
theorem coendInnerDesc_ιCurry (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    EndKan.Coend.ιCurry (coendSlice F d) c ≫ coendInnerDesc F d = EndKan.Coend.ι F (c, d) := by
  delta coendInnerDesc
  exact EndKan.Coend.desc_ιCurry (F := coendSlice F d)
    (ω := EndKan.Coend.DinaturalTransformation.ofDiagonal
      (fun c' => EndKan.Coend.ι F (c', d))
      (by
        intro c' c'' g
        exact EndKan.Coend.ι_dinatural (F := F) (f := g ×ₘ 𝟙 d))) c

noncomputable def coendInnerApp (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))] :
    ((EndKan.Coend.coendBifunctor (coendSlice F d)).obj (op c)).obj c ⟶ coendInnerObj F d' :=
  (congrArg (fun W => W ⟶ coendInnerObj F d')
      (EndKan.Coend.coendDiagonal (F := coendSlice F d) c)).mpr
    (coendSliceOpCovToSlice F c f ≫ coendInnerι F d' c)

@[simp]
theorem coendInnerApp_eq (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))] :
    coendInnerApp F c f =
      (congrArg (fun W => W ⟶ coendInnerObj F d')
          (EndKan.Coend.coendDiagonal (F := coendSlice F d) c)).mpr
        (coendSliceOpCovToSlice F c f ≫ coendInnerι F d' c) := rfl

@[reassoc]
theorem coendInnerApp_eq_slice (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))] :
    coendInnerApp F c f =
      coendSliceOpCovToSlice F c f ≫ coendInnerι F d' c := by
  rw [coendInnerApp_eq, congrArg_mpr_hom_left]
  exact EndKan.Coend.eqToHom_symm_comp_mpr_diagonal (F := coendSlice F d) (c := c)
    (X := coendInnerObj F d') (f := coendSliceOpCovToSlice F c f ≫ coendInnerι F d' c)

@[reassoc]
theorem coendInnerApp_eq_opCovIso (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))] :
    coendInnerApp F c f =
      eqToHom (coendSlice_obj F d c) ≫
        coendSliceOpCovIso F c d d' f ≫
        eqToHom (coendSlice_obj F d' c).symm ≫
        coendInnerι F d' c := by
  rw [coendInnerApp_eq_slice F c f, coendSliceOpCovToSlice_eq_opCovIso F c f]
  simp only [Category.assoc]

@[reassoc]
theorem eqToHom_post_coendInnerιWedge_desc (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    eqToHom (coendSlice_obj F d c) ≫ coendInnerιWedge F d c ≫ coendInnerDesc F d =
      coendInnerιWedge F d c ≫ coendInnerDesc F d := by
  have h :
      eqToHom (coendSlice_obj F d c) ≫ coendInnerιWedge F d c = coendInnerι F d c := by
    rw [coendInnerιWedge_eq F d c]
    exact (eqToIso (coendSlice_obj F d c)).hom_inv_id_assoc (coendInnerι F d c)
  rw [← Category.assoc, h, coendInnerDesc_ι F d c, ← coendInnerDesc_ιWedge F d c]

theorem coendSlice_eqToHom_post_ιWedge (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D) (c : C)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    eqToHom (coendSlice_obj F d c) ≫ EndKan.Coend.ι F (c, d) =
      coendInnerιWedge F d c ≫ coendInnerDesc F d := by
  rw [← coendInnerDesc_ιWedge F d c]
  exact eqToHom_post_coendInnerιWedge_desc F d c

@[reassoc]
theorem coendInnerApp_comp_desc (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] :
    coendInnerApp F c f ≫ coendInnerDesc F d' =
      coendInnerιWedge F d c ≫ coendInnerDesc F d := by
  rw [coendInnerApp_eq_slice F c f]
  exact (coendSlice_post_ι F d' c (coendSliceOpCovToSlice F c f)).trans <|
    (coendSliceOpCovToSlice_post_ι F c d d' f).trans <|
      coendSlice_eqToHom_post_ιWedge F d c

theorem coendInnerApp_dinatural (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (c c' : C) (g : c ⟶ c')
    {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [Mono (coendInnerDesc F d')] :
    ((EndKan.Coend.coendBifunctor (coendSlice F d)).map g.op).app c ≫ coendInnerApp F c f =
      ((EndKan.Coend.coendBifunctor (coendSlice F d)).obj (op c')).map g ≫ coendInnerApp F c' f := by
  apply (cancel_mono (coendInnerDesc F d')).mp
  rw [Category.assoc, coendInnerApp_comp_desc F c f]
  rw [Category.assoc, coendInnerApp_comp_desc F c' f]
  rw [coendInnerDesc_ιWedge F d c, coendInnerDesc_ιWedge F d c']
  exact EndKan.Coend.ι_dinatural (F := F) (f := g ×ₘ 𝟙 d)

noncomputable def coendInnerMapData (F : (C × D) × (C × D)ᵒᵖ ⥤ E) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [Mono (coendInnerDesc F d')] :
    EndKan.Coend.DinaturalTransformation (coendSlice F d) (coendInnerObj F d') where
  app := fun c => coendInnerApp F c f
  dinaturality := by
    intro c c' g
    exact coendInnerApp_dinatural F c c' g f

noncomputable def coendInnerMap (F : (C × D) × (C × D)ᵒᵖ ⥤ E) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [Mono (coendInnerDesc F d')] :
    coendInnerObj F d ⟶ coendInnerObj F d' :=
  EndKan.Coend.desc (coendInnerMapData F f)

theorem coendInner_hom_ext (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d d' : D)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))]
    {m n : coendInnerObj F d ⟶ coendInnerObj F d'}
    (h : ∀ c : C, coendInnerι F d c ≫ m = coendInnerι F d c ≫ n) : m = n := by
  apply EndKan.Coend.uniq (F := coendSlice F d)
  intro c
  rw [coendInnerιCurry_eq F d c, Category.assoc, h c, ← Category.assoc, ← coendInnerιCurry_eq F d c]

theorem coendInnerMap_spec (F : (C × D) × (C × D)ᵒᵖ ⥤ E) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [Mono (coendInnerDesc F d')] :
    coendInnerDesc F d = coendInnerMap F f ≫ coendInnerDesc F d' := by
  apply EndKan.Coend.uniq (F := coendSlice F d)
  intro c
  have h₁ :
      EndKan.Coend.ιCurry (coendSlice F d) c ≫ coendInnerDesc F d = EndKan.Coend.ι F (c, d) :=
    coendInnerDesc_ιCurry F d c
  have h₂ :
      EndKan.Coend.ι F (c, d) = coendInnerιWedge F d c ≫ coendInnerDesc F d :=
    (coendInnerDesc_ιWedge F d c).symm
  have h₃ :
      coendInnerιWedge F d c ≫ coendInnerDesc F d = coendInnerApp F c f ≫ coendInnerDesc F d' :=
    (coendInnerApp_comp_desc F c f).symm
  have h₄ :
      coendInnerApp F c f ≫ coendInnerDesc F d' =
        EndKan.Coend.ιCurry (coendSlice F d) c ≫ coendInnerMap F f ≫ coendInnerDesc F d' := by
    suffices h :
        coendInnerApp F c f =
          EndKan.Coend.ιCurry (coendSlice F d) c ≫ coendInnerMap F f by
      rw [← Category.assoc, h]
    rw [show coendInnerMap F f = EndKan.Coend.desc (coendInnerMapData F f) from rfl]
    exact (EndKan.Coend.desc_ιCurry (ω := coendInnerMapData F f) (F := coendSlice F d) c).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

@[reassoc (attr := simp)]
theorem coendInnerDesc_natural (F : (C × D) × (C × D)ᵒᵖ ⥤ E) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [Mono (coendInnerDesc F d')] :
    coendInnerMap F f ≫ coendInnerDesc F d' = coendInnerDesc F d :=
  (coendInnerMap_spec F f).symm

theorem coendInnerMap_unique (F : (C × D) × (C × D)ᵒᵖ ⥤ E) {d d' : D} (f : d ⟶ d')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [Mono (coendInnerDesc F d')]
    {m : coendInnerObj F d ⟶ coendInnerObj F d'}
    (h : coendInnerDesc F d = m ≫ coendInnerDesc F d') : m = coendInnerMap F f := by
  apply coendInner_hom_ext (F := F) (d := d) (d' := d')
  intro c
  apply (cancel_mono (coendInnerDesc F d')).mp
  rw [Category.assoc, Category.assoc, ← coendInnerMap_spec F f, ← h, coendInnerDesc_ι F d c]

@[simp]
theorem coendInnerMap_id (F : (C × D) × (C × D)ᵒᵖ ⥤ E) (d : D)
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [Mono (coendInnerDesc F d)] :
    coendInnerMap F (𝟙 d) = 𝟙 _ := by
  exact (coendInnerMap_unique F (𝟙 d) ((Category.id_comp (coendInnerDesc F d)).symm)).symm

theorem coendInnerMap_comp (F : (C × D) × (C × D)ᵒᵖ ⥤ E) {d d' d'' : D} (f : d ⟶ d') (g : d' ⟶ d'')
    [CoendSliceContrIso F]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d'))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d''))]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [Mono (coendInnerDesc F d')]
    [Mono (coendInnerDesc F d'')] :
    coendInnerMap F (f ≫ g) = coendInnerMap F f ≫ coendInnerMap F g := by
  symm
  apply coendInnerMap_unique F (f ≫ g)
  rw [coendInnerMap_spec F f, coendInnerMap_spec F g, Category.assoc]

end EndKan.Fubini
