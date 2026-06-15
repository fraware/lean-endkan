import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.EpiMono
import EndKan.End.Core
import EndKan.End.BetaEta

namespace EndKan.Fubini

set_option linter.tacticCheckInstances false

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Prod
open Opposite
open scoped Prod

universe u v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

abbrev EndIdx (C D : Type u) [Category C] [Category D] := Prod ((C × D)ᵒᵖ) (C × D)

/-- Canonical diagonal index; defeq to `(op (c, d), c, d)` used by `EndKan.End.π F (c, d)`. -/
abbrev endWedge (c : C) (d : D) : EndIdx C D := (op (c, d), c, d)

abbrev endOffCov (c : C) (d d' : D) : EndIdx C D := (op (c, d), c, d')

@[simp] theorem endWedge_eq (c : C) (d : D) : endWedge c d = (op (c, d), (c, d)) := rfl

@[simp]
theorem endWedge_eq_op (cd : C × D) : endWedge cd.1 cd.2 = (op cd, cd) := rfl

@[simp] theorem endOffCov_eq (c : C) (d d' : D) : endOffCov c d d' = (op (c, d), (c, d')) := rfl

@[simp] theorem endπ_obj_eq (F : EndIdx C D ⥤ E) (c : C) (d : D)
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    EndKan.End.π F (c, d) = EndKan.End.π F (c, d) := rfl

abbrev endSliceEmbed (d : D) : Cᵒᵖ × C ⥤ EndIdx C D where
  obj pq := (op (pq.1.unop, d), pq.2, d)
  map g := ((g.1.unop ×ₘ 𝟙 d).op, g.2 ×ₘ 𝟙 d)
  map_id := by
    intro pq
    apply Prod.hom_ext
    · apply Quiver.Hom.unop_inj; simp
    · simp [prod_id]
  map_comp := by
    intro pq pq' pq'' f g
    apply Prod.hom_ext
    · apply Quiver.Hom.unop_inj; simp [prod_comp]
    · simp [prod_comp]

@[simp]
theorem endSliceEmbed_obj (d : D) (c : C) :
    (endSliceEmbed d).obj (op c, c) = endWedge c d := rfl

abbrev endSlice (F : EndIdx C D ⥤ E) (d : D) : Cᵒᵖ × C ⥤ E :=
  endSliceEmbed d ⋙ F

@[simp]
theorem endSlice_as_comp (F : EndIdx C D ⥤ E) (d : D) :
    endSlice F d = endSliceEmbed d ⋙ F := rfl

@[simp]
theorem endSlice_obj (F : EndIdx C D ⥤ E) (d : D) (c : C) :
    (endSlice F d).obj (op c, c) = F.obj (endWedge c d) := rfl

noncomputable abbrev endInnerObj (F : EndIdx C D ⥤ E) (d : D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))] : E :=
  EndKan.End.EndObj (endSlice F d)

@[simp]
theorem endInnerObj_eq (F : EndIdx C D ⥤ E) (d : D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))] :
    endInnerObj F d = EndKan.End.EndObj (endSlice F d) := rfl

noncomputable def endInnerπ (F : EndIdx C D ⥤ E) (d : D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))] (c : C) :
    endInnerObj F d ⟶ F.obj (endWedge c d) :=
  EndKan.End.π (endSlice F d) c

noncomputable def endInnerLift (F : EndIdx C D ⥤ E) (d : D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    EndKan.End.EndObj F ⟶ endInnerObj F d :=
  EndKan.End.lift ⟨(fun c => EndKan.End.π F (c, d)), by
    intro c c' f
    dsimp [EndKan.End.π, EndKan.End.endBifunctor]
    exact Limits.end_.condition (EndKan.End.endBifunctor F) (f ×ₘ 𝟙 d)⟩

@[simp]
theorem endInnerπ_π (F : EndIdx C D ⥤ E) (d : D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))] (c : C) :
    endInnerπ F d c = EndKan.End.π (endSlice F d) c := rfl

@[reassoc (attr := simp)]
theorem endInnerLift_π (F : EndIdx C D ⥤ E) (d : D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] (c : C) :
    endInnerLift F d ≫ endInnerπ F d c = EndKan.End.π F (c, d) := by
  dsimp only [endInnerLift, endInnerπ]
  exact EndKan.End.lift_π _ c

@[reassoc]
theorem endInnerLift_π_slice (F : EndIdx C D ⥤ E) (d : D) (c : C)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    endInnerLift F d ≫ EndKan.End.π (endSlice F d) c = EndKan.End.π F (c, d) :=
  endInnerLift_π F d c

/-- Wedge-facing inner projection (for composites into the product profunctor). -/
noncomputable def endInnerπWedge (F : EndIdx C D ⥤ E) (cd : C × D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F cd.2))] :
    endInnerObj F cd.2 ⟶ F.obj (op cd, cd) :=
  endInnerπ F cd.2 cd.1 ≫ eqToHom (congrArg F.obj (endWedge_eq_op cd))

@[simp]
theorem endInnerπWedge_eq (F : EndIdx C D ⥤ E) (cd : C × D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F cd.2))] :
    endInnerπWedge F cd = endInnerπ F cd.2 cd.1 ≫ eqToHom (congrArg F.obj (endWedge_eq_op cd)) := rfl

theorem endπ_eq_op_wedge (F : EndIdx C D ⥤ E) (cd : C × D)
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    EndKan.End.π F (cd.1, cd.2) ≫ eqToHom (congrArg F.obj (endWedge_eq_op cd)) =
      EndKan.End.π F cd := by
  cases cd with
  | mk c d =>
    simp [endWedge_eq_op, eqToHom_trans, Category.comp_id]

@[reassoc]
theorem endInnerLift_πWedge (F : EndIdx C D ⥤ E) (cd : C × D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F cd.2))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    endInnerLift F cd.2 ≫ endInnerπWedge F cd = EndKan.End.π F cd := by
  rw [endInnerπWedge, ← Category.assoc, endInnerLift_π, endπ_eq_op_wedge]

@[simp]
theorem endInnerπWedge_π (F : EndIdx C D ⥤ E) (c : C) (d : D)
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)] :
    endInnerπWedge F (c, d) = EndKan.End.π (endSlice F d) c := by
  rw [← endInnerπ_π]
  apply (cancel_epi (endInnerLift F d)).1
  calc
    endInnerLift F d ≫ endInnerπWedge F (c, d) = EndKan.End.π F (c, d) := endInnerLift_πWedge F (c, d)
    _ = endInnerLift F d ≫ endInnerπ F d c := (endInnerLift_π F d c).symm

section sliceMaps

variable (F : EndIdx C D ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')
variable [Limits.HasEnd (EndKan.End.endBifunctor F)]

noncomputable def endSliceCov : F.obj (endWedge c d) ⟶ F.obj (endOffCov c d d') :=
  ((EndKan.End.endBifunctor F).obj (op (c, d))).map (𝟙 c ×ₘ f)

noncomputable def endSliceContrMap : F.obj (endWedge c d') ⟶ F.obj (endOffCov c d d') :=
  ((EndKan.End.endBifunctor F).map (𝟙 c ×ₘ f).op).app (c, d')

@[reassoc (attr := simp)]
theorem endSlice_cov_contr :
    EndKan.End.π F (c, d) ≫ endSliceCov F c d d' f =
      EndKan.End.π F (c, d') ≫ endSliceContrMap F c d d' f := by
  dsimp [endSliceCov, endSliceContrMap, EndKan.End.π, EndKan.End.endBifunctor, endWedge, endOffCov]
  exact Limits.end_.condition (EndKan.End.endBifunctor F) (𝟙 c ×ₘ f)

theorem end_into_jointMono (F : EndIdx C D ⥤ E) [Limits.HasEnd (EndKan.End.endBifunctor F)]
    {X : E} {g h : X ⟶ EndKan.End.EndObj F}
    (H : ∀ cd : C × D, g ≫ EndKan.End.π F cd = h ≫ EndKan.End.π F cd) : g = h := by
  dsimp [EndKan.End.EndObj, EndKan.End.endBifunctor]
  exact Limits.end_.hom_ext (f := g) (g := h) H

noncomputable def endSliceOpCovIso [IsIso (endSliceContrMap F c d d' f)] :
    F.obj (endWedge c d) ⟶ F.obj (endWedge c d') :=
  endSliceCov F c d d' f ≫ CategoryTheory.inv (endSliceContrMap F c d d' f)

theorem endSliceOpCovIso_sec [IsIso (endSliceContrMap F c d d' f)] :
    EndKan.End.π F (c, d) ≫ endSliceOpCovIso F c d d' f = EndKan.End.π F (c, d') := by
  dsimp [endSliceOpCovIso]
  rw [← Category.assoc, endSlice_cov_contr F c d d' f, IsIso.comp_inv_eq]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceOpCovIso_comp_contr [IsIso (endSliceContrMap F c d d' f)] :
    endSliceOpCovIso F c d d' f ≫ endSliceContrMap F c d d' f = endSliceCov F c d d' f := by
  simp [endSliceOpCovIso, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endOffCov_wedge_ext [IsIso (endSliceContrMap F c d d' f)]
    {u v : F.obj (endOffCov c d d') ⟶ F.obj (endWedge c d')}
    (_ : endSliceCov F c d d' f ≫ u = endSliceCov F c d d' f ≫ v)
    (h₂ : endSliceContrMap F c d d' f ≫ u = endSliceContrMap F c d d' f ≫ v) : u = v := by
  have h := congrArg (CategoryTheory.inv (endSliceContrMap F c d d' f) ≫ ·) h₂
  simpa [Category.assoc, IsIso.inv_hom_id, Category.id_comp] using h

noncomputable def endSliceInvContr [IsIso (endSliceCov F c d d' f)] [IsIso (endSliceContrMap F c d d' f)] :
    F.obj (endOffCov c d d') ⟶ F.obj (endWedge c d') :=
  CategoryTheory.inv (endSliceCov F c d d' f) ≫ endSliceOpCovIso F c d d' f

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceInvContr_eq_invContr [IsIso (endSliceCov F c d d' f)] [IsIso (endSliceContrMap F c d d' f)] :
    endSliceInvContr F c d d' f = CategoryTheory.inv (endSliceContrMap F c d d' f) := by
  apply endOffCov_wedge_ext (F := F) (c := c) (d := d) (d' := d') (f := f)
  · dsimp [endSliceInvContr, endSliceOpCovIso]
    rw [← Category.assoc, IsIso.hom_inv_id (endSliceCov F c d d' f), Category.id_comp]
  · dsimp only [endSliceInvContr, endSliceOpCovIso]
    rw [← Category.assoc (CategoryTheory.inv (endSliceCov F c d d' f)) (endSliceCov F c d d' f)
        (CategoryTheory.inv (endSliceContrMap F c d d' f)),
      IsIso.inv_hom_id (endSliceCov F c d d' f), Category.id_comp]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceContrMap_inv_hom [IsIso (endSliceCov F c d d' f)] [IsIso (endSliceContrMap F c d d' f)] :
    endSliceInvContr F c d d' f ≫ endSliceContrMap F c d d' f = 𝟙 (F.obj (endOffCov c d d')) := by
  dsimp only [endSliceInvContr]
  rw [Category.assoc, endSliceOpCovIso_comp_contr, IsIso.inv_hom_id]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endOffCov_wedge_ext' (hContr : IsIso (endSliceContrMap F c d d' f))
    {u v : F.obj (endOffCov c d d') ⟶ F.obj (endWedge c d')}
    (_ : endSliceCov F c d d' f ≫ u = endSliceCov F c d d' f ≫ v)
    (h₂ : endSliceContrMap F c d d' f ≫ u = endSliceContrMap F c d d' f ≫ v) : u = v := by
  have h := congrArg (fun x => @CategoryTheory.inv _ _ _ _ (endSliceContrMap F c d d' f) hContr ≫ x) h₂
  have hu : @CategoryTheory.inv _ _ _ _ (endSliceContrMap F c d d' f) hContr ≫
      endSliceContrMap F c d d' f ≫ u = u := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hv : @CategoryTheory.inv _ _ _ _ (endSliceContrMap F c d d' f) hContr ≫
      endSliceContrMap F c d d' f ≫ v = v := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hu, hv] at h; exact h

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceContrMap_hom_inv [IsIso (endSliceCov F c d d' f)] [IsIso (endSliceContrMap F c d d' f)] :
    endSliceContrMap F c d d' f ≫ endSliceInvContr F c d d' f = 𝟙 (F.obj (endWedge c d')) := by
  rw [endSliceInvContr_eq_invContr, IsIso.hom_inv_id]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceOpCovIso_isIso [IsIso (endSliceCov F c d d' f)] [IsIso (endSliceContrMap F c d d' f)] :
    IsIso (endSliceOpCovIso F c d d' f) := by
  simpa [endSliceOpCovIso] using
    (inferInstance : IsIso (endSliceCov F c d d' f ≫ CategoryTheory.inv (endSliceContrMap F c d d' f)))

noncomputable def endSliceCovInv [IsIso (endSliceCov F c d d' f)] [IsIso (endSliceContrMap F c d d' f)] :
    F.obj (endOffCov c d d') ⟶ F.obj (endWedge c d) :=
  endSliceInvContr F c d d' f ≫
    @CategoryTheory.inv _ _ _ _ (endSliceOpCovIso F c d d' f)
      (endSliceOpCovIso_isIso F c d d' f)

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceCov_inv_hom [IsIso (endSliceCov F c d d' f)] [IsIso (endSliceContrMap F c d d' f)] :
    endSliceCovInv F c d d' f ≫ endSliceCov F c d d' f = 𝟙 (F.obj (endOffCov c d d')) := by
  have hOpCov := endSliceOpCovIso_isIso F c d d' f
  have hInvContr := (endSliceInvContr_eq_invContr F c d d' f).symm
  dsimp only [endSliceCovInv, endSliceInvContr]
  have htail :
      @CategoryTheory.inv _ _ _ _ (endSliceOpCovIso F c d d' f) hOpCov ≫ endSliceCov F c d d' f =
        endSliceContrMap F c d d' f := by
    rw [← endSliceOpCovIso_comp_contr F c d d' f, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  simp only [Category.assoc, htail, endSliceOpCovIso_comp_contr F c d d' f, IsIso.inv_hom_id]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceCov_hom_inv [IsIso (endSliceCov F c d d' f)] [IsIso (endSliceContrMap F c d d' f)] :
    endSliceCov F c d d' f ≫ endSliceCovInv F c d d' f = 𝟙 (F.obj (endWedge c d)) := by
  have hInvContr := (endSliceInvContr_eq_invContr F c d d' f).symm
  dsimp only [endSliceCovInv, endSliceInvContr]
  simp only [Category.assoc, hInvContr, endSliceOpCovIso, IsIso.hom_inv_id, Category.comp_id]

end sliceMaps

section sliceIsoPackaging

variable (F : EndIdx C D ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')

/-- Conditional `IsIso.mk` packaging from the lemma layer (not unconditional bootstrap). -/
@[reducible] noncomputable def endSliceContrIsoFromData (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    IsIso (endSliceContrMap F c d d' f) := by
  letI := hCov
  letI := hContr
  exact IsIso.mk ⟨endSliceInvContr F c d d' f, endSliceContrMap_hom_inv F c d d' f,
    endSliceContrMap_inv_hom F c d d' f⟩

@[reducible] noncomputable def endSliceCovIsoFromData (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    IsIso (endSliceCov F c d d' f) := by
  letI := hCov
  letI := hContr
  exact IsIso.mk ⟨endSliceCovInv F c d d' f, endSliceCov_hom_inv F c d d' f,
    endSliceCov_inv_hom F c d d' f⟩

end sliceIsoPackaging

/-- Joint separation for maps into `F.obj (endOffCov c d d')`. -/
class EndSliceJointMono (F : EndIdx C D ⥤ E) where
  ext :
    ∀ (c : C) (d d' : D) (f : d ⟶ d') {u v : F.obj (endOffCov c d d') ⟶ F.obj (endWedge c d')}
      (_ : endSliceCov F c d d' f ≫ u = endSliceCov F c d d' f ≫ v)
      (h₂ : endSliceContrMap F c d d' f ≫ u = endSliceContrMap F c d d' f ≫ v), u = v

section sliceIsoBootstrap

variable (F : EndIdx C D ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')
variable [Limits.HasEnd (EndKan.End.endBifunctor F)]

/-!
rc1 blocker (Attempt 4): unconditional / seeded mutual `noncomputable def` cannot close:
* `mutual instance` — termination failure (no structural argument);
* seeded `mutual def` with `hCov` — well-founded recursion failure (same-level self-reference);
* `partial def` on generalized `∀ …, IsIso _` — `Nonempty (IsIso _)` check fails.
Lemma stack through `endSliceCov_hom_inv` / `endSliceCov_inv_hom` is unconditional.

Joint-mono closure (Attempt 5): `[IsIso (endSliceCov F c d d' f)]` + `[EndSliceJointMono F]` does not
determine `[IsIso (endSliceContrMap F c d d' f)]`. The candidate inverse `endSliceInvContr` has
codomain `F.obj (endWedge c d')` but requires both leg isos to type-check; `endSliceInvContr_eq_invContr`,
`endSliceContrMap_hom_inv`, and `endSliceContrMap_inv_hom` all invoke `endOffCov_wedge_ext'` with an
`IsIso (endSliceContrMap …)` argument. Joint mono only proves equality of parallel maps into
`endWedge c d'`, not existence of a two-sided inverse for `endSliceContrMap`. Consumer path:
`allEndSliceContrIsoOfData` on concrete `F` (see `EndKan.Fubini.Examples`).
-/

end sliceIsoBootstrap

/-- Every contravariant slice leg for `F` is an isomorphism (supplied for nested Fubini). -/
class AllEndSliceContrIso (F : EndIdx C D ⥤ E) where
  iso : ∀ (c : C) (d d' : D) (f : d ⟶ d'), IsIso (endSliceContrMap F c d d' f)

section sliceIsoJointMono

variable (F : EndIdx C D ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')
variable [EndSliceJointMono F]

omit [EndSliceJointMono F] in
/-- Contr leg iso from bilateral data, using the unconditional lemma layer. -/
theorem endSliceContrMap_isIso_of_jointMono (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    IsIso (endSliceContrMap F c d d' f) :=
  endSliceContrIsoFromData F c d d' f hCov hContr

/-- Package `AllEndSliceContrIso` from per-leg cov/contr iso data (not an empty class assumption). -/
@[reducible] def allEndSliceContrIsoOfData {F : EndIdx C D ⥤ E}
    (h :
      ∀ (c : C) (d d' : D) (f : d ⟶ d'),
        IsIso (endSliceCov F c d d' f) ∧ IsIso (endSliceContrMap F c d d' f)) :
    AllEndSliceContrIso F where
  iso c d d' f := endSliceContrIsoFromData F c d d' f (h c d d' f).1 (h c d d' f).2

/-- When every cov leg is iso and joint separation holds, supply contr iso data to close Fubini. -/
class EndSliceIsoData (F : EndIdx C D ⥤ E) [EndSliceJointMono F] extends AllEndSliceContrIso F where
  covIso : ∀ (c : C) (d d' : D) (f : d ⟶ d'), IsIso (endSliceCov F c d d' f)

end sliceIsoJointMono

noncomputable instance instEndSliceContrIsIso {F : EndIdx C D ⥤ E} (c : C) (d d' : D) (f : d ⟶ d')
    [AllEndSliceContrIso F] : IsIso (endSliceContrMap F c d d' f) :=
  AllEndSliceContrIso.iso (F := F) c d d' f

@[reassoc (attr := simp)]
theorem endInnerLift_comp_cov (F : EndIdx C D ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    endInnerLift F d ≫ endInnerπ F d c ≫ endSliceCov F c d d' f =
      endInnerLift F d' ≫ endInnerπ F d' c ≫ endSliceContrMap F c d d' f := by
  rw [← Category.assoc, endInnerLift_π F d c, endSlice_cov_contr F c d d' f,
    ← Category.assoc, ← endInnerLift_π F d' c]

@[reassoc (attr := simp)]
theorem endInnerLift_comp_opCov (F : EndIdx C D ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    endInnerLift F d ≫ endInnerπ F d c ≫ endSliceOpCovIso F c d d' f =
      endInnerLift F d' ≫ endInnerπ F d' c := by
  rw [← Category.assoc, endInnerLift_π F d c, endSliceOpCovIso_sec F c d d' f, ← endInnerLift_π F d' c]

/-- Repackage `endSliceOpCovIso` for composition with `endSlice F d'`. -/
noncomputable def endSliceOpCovToSlice (F : EndIdx C D ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [IsIso (endSliceContrMap F c d d' f)] :
    F.obj (endWedge c d) ⟶ (endSlice F d').obj (op c, c) :=
  endSliceOpCovIso F c d d' f ≫ eqToHom (endSlice_obj F d' c).symm

theorem endSliceOpCovToSlice_eq_opCovIso (F : EndIdx C D ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [IsIso (endSliceContrMap F c d d' f)] :
    endSliceOpCovToSlice F c f = endSliceOpCovIso F c d d' f := by
  dsimp [endSliceOpCovToSlice]
  exact Category.comp_id (endSliceOpCovIso F c d d' f)

@[reassoc]
theorem endInnerLift_comp_opCovToSlice (F : EndIdx C D ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    endInnerLift F d ≫ endInnerπ F d c ≫ endSliceOpCovToSlice F c f =
      endInnerLift F d' ≫ EndKan.End.π (endSlice F d') c := by
  refine (congrArg (fun ψ => endInnerLift F d ≫ endInnerπ F d c ≫ ψ)
    (endSliceOpCovToSlice_eq_opCovIso F c f)).trans ?_
  exact (endInnerLift_comp_opCov F c f).trans
    (congrArg (fun ψ => endInnerLift F d' ≫ ψ) (endInnerπ_π F d' c))

theorem endInnerApp_dinaturalSlice (F : EndIdx C D ⥤ E) (c c' : C) (g : c ⟶ c') {d d' : D}
    (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)] :
    endInnerπ F d c ≫ endSliceOpCovToSlice F c f ≫ (endSlice F d').map (𝟙 (op c) ×ₘ g) =
      endInnerπ F d c' ≫ endSliceOpCovToSlice F c' f ≫ (endSlice F d').map (g.op ×ₘ 𝟙 c') := by
  refine (cancel_epi (endInnerLift F d)).1 ?_
  rw [endInnerLift_comp_opCovToSlice_assoc, endInnerLift_comp_opCovToSlice_assoc]
  exact congrArg (fun ψ => endInnerLift F d' ≫ ψ) (EndKan.End.π_natural (F := endSlice F d') g)

theorem endInnerApp_dinatural (F : EndIdx C D ⥤ E) (c c' : C) (g : c ⟶ c') {d d' : D}
    (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)] :
    endInnerπ F d c ≫ endSliceOpCovIso F c d d' f ≫
        ((EndKan.End.endBifunctor (endSlice F d')).obj (op c)).map g =
      endInnerπ F d c' ≫ endSliceOpCovIso F c' d d' f ≫
        ((EndKan.End.endBifunctor (endSlice F d')).map g.op).app c' := by
  rw [EndKan.End.endBifunctor_obj_map, EndKan.End.endBifunctor_map_app]
  have h := endInnerApp_dinaturalSlice F c c' g f
  rw [endSliceOpCovToSlice_eq_opCovIso, endSliceOpCovToSlice_eq_opCovIso (c := c')] at h
  exact h

def EndInnerMapTarget (F : EndIdx C D ⥤ E) {d d' : D} (_f : d ⟶ d')
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] : Prop :=
  ∃ m, endInnerLift F d ≫ m = endInnerLift F d'

theorem endInner_hom_ext (F : EndIdx C D ⥤ E) {d d' : D}
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    {m n : endInnerObj F d ⟶ endInnerObj F d'}
    (h : ∀ c : C, m ≫ endInnerπ F d' c = n ≫ endInnerπ F d' c) : m = n := by
  apply EndKan.End.uniq (F := endSlice F d')
  intro c
  rw [← endInnerπ_π F d' c]
  exact h c

noncomputable def endInnerApp (F : EndIdx C D ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    endInnerObj F d ⟶ F.obj (endWedge c d') :=
  endInnerπ F d c ≫ endSliceOpCovIso F c d d' f

@[simp]
theorem endInnerApp_eq (F : EndIdx C D ⥤ E) (c : C) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)] :
    endInnerApp F c f =
      endInnerπ F d c ≫ endSliceOpCovIso F c d d' f := rfl

noncomputable def endInnerMapData (F : EndIdx C D ⥤ E) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)] :
    EndKan.End.DinaturalTransformation (endInnerObj F d) (endSlice F d') where
  app := fun c => endInnerπ F d c ≫ endSliceOpCovToSlice F c f
  dinaturality := by
    intro c c' g
    have h := endInnerApp_dinaturalSlice F c c' g f
    conv_lhs => rw [Category.assoc, EndKan.End.endBifunctor_obj_map]
    conv_rhs => rw [Category.assoc, EndKan.End.endBifunctor_map_app]
    exact h

noncomputable def endInnerMap (F : EndIdx C D ⥤ E) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)]
    [Epi (endInnerLift F d')] :
    endInnerObj F d ⟶ endInnerObj F d' :=
  EndKan.End.lift (F := endSlice F d') (endInnerMapData F f)

theorem endInnerMap_spec (F : EndIdx C D ⥤ E) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)]
    [Epi (endInnerLift F d')] :
    endInnerLift F d ≫ endInnerMap F f = endInnerLift F d' := by
  apply EndKan.End.uniq (F := endSlice F d')
  intro c
  calc
    (endInnerLift F d ≫ endInnerMap F f) ≫ EndKan.End.π (endSlice F d') c
        = endInnerLift F d ≫ endInnerMap F f ≫ EndKan.End.π (endSlice F d') c := by
          rw [Category.assoc]
    _ = endInnerLift F d ≫ (endInnerMapData F f).app c := by
          rw [show endInnerMap F f = EndKan.End.lift (endInnerMapData F f) from rfl]
          exact congrArg (fun ψ => endInnerLift F d ≫ ψ)
            (EndKan.End.lift_π (F := endSlice F d') (ω := endInnerMapData F f) c)
    _ = endInnerLift F d ≫ endInnerπ F d c ≫ endSliceOpCovToSlice F c f := by
          rfl
    _ = endInnerLift F d' ≫ EndKan.End.π (endSlice F d') c := by
          rw [endInnerLift_comp_opCovToSlice]

theorem endInnerLift_cancel (F : EndIdx C D ⥤ E) (d d' : D)
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)]
    {u v : endInnerObj F d ⟶ endInnerObj F d'}
    (h : endInnerLift F d ≫ u = endInnerLift F d ≫ v) : u = v :=
  (cancel_epi (endInnerLift F d)).1 h

theorem endInnerMap_unique (F : EndIdx C D ⥤ E) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)]
    [Epi (endInnerLift F d')]
    {m : endInnerObj F d ⟶ endInnerObj F d'}
    (h : endInnerLift F d ≫ m = endInnerLift F d') : m = endInnerMap F f :=
  (cancel_epi (endInnerLift F d)).1 (h.trans (endInnerMap_spec F f).symm)

@[reassoc]
theorem endInnerLift_natural (F : EndIdx C D ⥤ E) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)]
    [Epi (endInnerLift F d')] :
    endInnerLift F d ≫ endInnerMap F f = endInnerLift F d' :=
  endInnerMap_spec F f

theorem endInnerπWedge_dinatural (F : EndIdx C D ⥤ E) {cd cd' : C × D} (fg : cd ⟶ cd')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F cd.2))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F cd'.2))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F cd.2)]
    [Epi (endInnerLift F cd'.2)] :
    endInnerπWedge F cd ≫ F.map (𝟙 (op cd) ×ₘ fg) =
      endInnerMap F fg.2 ≫ endInnerπWedge F cd' ≫ F.map (fg.op ×ₘ 𝟙 cd') := by
  refine (cancel_epi (endInnerLift F cd.2)).1 ?_
  have h := EndKan.End.π_natural (F := F) fg
  simp only [EndKan.End.endBifunctor_obj_map, EndKan.End.endBifunctor_map_app] at h
  calc
    endInnerLift F cd.2 ≫ endInnerπWedge F cd ≫ F.map (𝟙 (op cd) ×ₘ fg)
        = EndKan.End.π F cd ≫ F.map (𝟙 (op cd) ×ₘ fg) := by
            rw [← Category.assoc, endInnerLift_πWedge]
    _ = EndKan.End.π F cd' ≫ F.map (fg.op ×ₘ 𝟙 cd') := h
    _ = endInnerLift F cd'.2 ≫ endInnerπWedge F cd' ≫ F.map (fg.op ×ₘ 𝟙 cd') := by
          rw [← Category.assoc, ← endInnerLift_πWedge]
    _ = endInnerLift F cd.2 ≫ endInnerMap F fg.2 ≫ endInnerπWedge F cd' ≫ F.map (fg.op ×ₘ 𝟙 cd') := by
          rw [← endInnerLift_natural (F := F) (f := fg.2), Category.assoc]

theorem endInnerπWedge_dinatural_curry (F : EndIdx C D ⥤ E) {cd cd' : C × D} (fg : cd ⟶ cd')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F cd.2))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F cd'.2))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F cd.2)]
    [Epi (endInnerLift F cd'.2)] :
    endInnerπWedge F cd ≫ ((EndKan.End.endBifunctor F).obj (op cd)).map fg =
      endInnerMap F fg.2 ≫ endInnerπWedge F cd' ≫ ((EndKan.End.endBifunctor F).map fg.op).app cd' := by
  convert endInnerπWedge_dinatural F fg using 1

theorem endInnerMapTarget (F : EndIdx C D ⥤ E) {d d' : D} (f : d ⟶ d')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)]
    [Epi (endInnerLift F d')] :
    EndInnerMapTarget F f :=
  ⟨endInnerMap F f, endInnerMap_spec F f⟩

@[simp]
theorem endInnerMap_id (F : EndIdx C D ⥤ E) (d : D)
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)] :
    endInnerMap F (𝟙 d) = 𝟙 _ := by
  exact (endInnerMap_unique F (𝟙 d) (Category.comp_id _)).symm

theorem endInnerMap_comp (F : EndIdx C D ⥤ E) {d d' d'' : D} (f : d ⟶ d') (g : d' ⟶ d'')
    [AllEndSliceContrIso F]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d'))]
    [Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d''))]
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [Epi (endInnerLift F d)]
    [Epi (endInnerLift F d')]
    [Epi (endInnerLift F d'')] :
    endInnerMap F (f ≫ g) = endInnerMap F f ≫ endInnerMap F g := by
  exact (endInnerMap_unique F (f ≫ g) (by
    rw [← Category.assoc, endInnerMap_spec, endInnerMap_spec])).symm

end EndKan.Fubini
