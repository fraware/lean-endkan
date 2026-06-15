import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Opposites
import EndKan.End.Core
import EndKan.End.BetaEta

/-!
Minimal EndIdx slice iso bootstrap harness (reference for `EndKan.Fubini.Slice`).
Attempt 3 joint-mono: manual `IsIso.mk`, calc hom_inv, mutual noncomputable instance.
-/

namespace Scratch.SliceIsoMin

open CategoryTheory
open CategoryTheory.Functor
open Opposite
open scoped Prod

universe u v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

abbrev EndIdx (C D : Type u) [Category C] [Category D] := Prod ((C × D)ᵒᵖ) (C × D)

abbrev endWedge (c : C) (d : D) : EndIdx C D := (op (c, d), c, d)

abbrev endOffCov (c : C) (d d' : D) : EndIdx C D := (op (c, d), c, d')

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

noncomputable def endSliceOpCovIso (hContr : IsIso (endSliceContrMap F c d d' f)) :
    F.obj (endWedge c d) ⟶ F.obj (endWedge c d') :=
  endSliceCov F c d d' f ≫ CategoryTheory.inv (endSliceContrMap F c d d' f)

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceOpCovIso_comp_contr (hContr : IsIso (endSliceContrMap F c d d' f)) :
    endSliceOpCovIso F c d d' f hContr ≫ endSliceContrMap F c d d' f =
      endSliceCov F c d d' f := by
  simp [endSliceOpCovIso, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

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

noncomputable def endSliceInvContr (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    F.obj (endOffCov c d d') ⟶ F.obj (endWedge c d') :=
  CategoryTheory.inv (endSliceCov F c d d' f) ≫ endSliceOpCovIso F c d d' f hContr

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceInvContr_eq_invContr (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    endSliceInvContr F c d d' f hCov hContr =
      CategoryTheory.inv (endSliceContrMap F c d d' f) := by
  refine endOffCov_wedge_ext' (F := F) (c := c) (d := d) (d' := d') (f := f) hContr ?_ ?_
  · dsimp [endSliceInvContr, endSliceOpCovIso]
    rw [← Category.assoc, IsIso.hom_inv_id (endSliceCov F c d d' f), Category.id_comp]
  · dsimp only [endSliceInvContr, endSliceOpCovIso]
    rw [← Category.assoc (CategoryTheory.inv (endSliceCov F c d d' f)) (endSliceCov F c d d' f)
        (CategoryTheory.inv (endSliceContrMap F c d d' f)),
      IsIso.inv_hom_id (endSliceCov F c d d' f), Category.id_comp]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceContrMap_hom_inv (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    endSliceContrMap F c d d' f ≫ endSliceInvContr F c d d' f hCov hContr =
      𝟙 (F.obj (endWedge c d')) := by
  rw [endSliceInvContr_eq_invContr F c d d' f hCov hContr, IsIso.hom_inv_id]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceContrMap_inv_hom (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    endSliceInvContr F c d d' f hCov hContr ≫ endSliceContrMap F c d d' f =
      𝟙 (F.obj (endOffCov c d d')) := by
  dsimp only [endSliceInvContr]
  rw [Category.assoc, endSliceOpCovIso_comp_contr F c d d' f hContr, IsIso.inv_hom_id]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceOpCovIso_isIso (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    IsIso (endSliceOpCovIso F c d d' f hContr) := by
  simpa [endSliceOpCovIso] using
    (inferInstance : IsIso (endSliceCov F c d d' f ≫ CategoryTheory.inv (endSliceContrMap F c d d' f)))

noncomputable def endSliceCovInv (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    F.obj (endOffCov c d d') ⟶ F.obj (endWedge c d) :=
  endSliceInvContr F c d d' f hCov hContr ≫
    @CategoryTheory.inv _ _ _ _ (endSliceOpCovIso F c d d' f hContr)
      (endSliceOpCovIso_isIso F c d d' f hCov hContr)

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceCov_inv_hom (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    endSliceCovInv F c d d' f hCov hContr ≫ endSliceCov F c d d' f =
      𝟙 (F.obj (endOffCov c d d')) := by
  have hOpCov := endSliceOpCovIso_isIso F c d d' f hCov hContr
  have hInvContr := (endSliceInvContr_eq_invContr F c d d' f hCov hContr).symm
  dsimp only [endSliceCovInv, endSliceInvContr]
  have htail :
      @CategoryTheory.inv _ _ _ _ (endSliceOpCovIso F c d d' f hContr) hOpCov ≫ endSliceCov F c d d' f =
        endSliceContrMap F c d d' f := by
    rw [← endSliceOpCovIso_comp_contr F c d d' f hContr, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  simp only [Category.assoc, htail, endSliceOpCovIso_comp_contr F c d d' f hContr, IsIso.inv_hom_id]

omit [Limits.HasEnd (EndKan.End.endBifunctor F)] in
theorem endSliceCov_hom_inv (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    endSliceCov F c d d' f ≫ endSliceCovInv F c d d' f hCov hContr =
      𝟙 (F.obj (endWedge c d)) := by
  have hInvContr := (endSliceInvContr_eq_invContr F c d d' f hCov hContr).symm
  dsimp only [endSliceCovInv, endSliceInvContr]
  simp only [Category.assoc, hInvContr, endSliceOpCovIso, IsIso.hom_inv_id, Category.comp_id]

end sliceMaps

section sliceIsoDefault

variable (F : EndIdx C D ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')
variable [Limits.HasEnd (EndKan.End.endBifunctor F)]

/-- Conditional `IsIso.mk` packaging from the lemma layer (not unconditional bootstrap). -/
@[reducible] noncomputable def endSliceContrIsoFromData (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    IsIso (endSliceContrMap F c d d' f) :=
  IsIso.mk ⟨endSliceInvContr F c d d' f hCov hContr,
    endSliceContrMap_hom_inv F c d d' f hCov hContr,
    endSliceContrMap_inv_hom F c d d' f hCov hContr⟩

@[reducible] noncomputable def endSliceCovIsoFromData (hCov : IsIso (endSliceCov F c d d' f))
    (hContr : IsIso (endSliceContrMap F c d d' f)) :
    IsIso (endSliceCov F c d d' f) :=
  IsIso.mk ⟨endSliceCovInv F c d d' f hCov hContr,
    endSliceCov_hom_inv F c d d' f hCov hContr,
    endSliceCov_inv_hom F c d d' f hCov hContr⟩

/-!
rc1 blocker (Attempt 3 joint-mono): unconditional mutual `noncomputable instance` / `partial def`
cannot close here:
* `mutual instance` — termination failure (no structural argument);
* `partial def` on generalized `∀ …, IsIso _` — `Nonempty (IsIso _)` check fails;
* `noncomputable def` / `opaque` self-reference — well-founded recursion failure.
Lemma stack through `endSliceCov_hom_inv` / `endSliceCov_inv_hom` is unconditional.
-/

#check endSliceContrIsoFromData F c d d' f
#check endSliceCovIsoFromData F c d d' f
#check endSliceOpCovIso_isIso F c d d' f

end sliceIsoDefault

end Scratch.SliceIsoMin
