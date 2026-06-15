import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Products.Basic
import EndKan.Fubini

/-!
Concrete profunctor instances for nested Fubini: constant functors on a one-object category.
Per-leg slice isomorphisms are packaged via `allEndSliceContrIsoOfData` / `coendSliceContrIsoOfData`.
-/

namespace EndKan.Fubini.Examples

set_option linter.tacticCheckInstances false

open CategoryTheory
open Opposite
open scoped Prod

universe u v

/-- One-object category used for concrete Fubini examples. -/
abbrev OneCat : Type u := PUnit

instance oneCat : Category.{v, u} OneCat where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

section ConstantEnd

variable {E : Type u} [Category.{v, u} E]

/-- Constant end profunctor on `EndIdx OneCat OneCat`. -/
def endConstProfunctor (X : E) : EndIdx OneCat OneCat ⥤ E where
  obj _ := X
  map _ := 𝟙 X
  map_id := by intro; simp
  map_comp := by intros; simp

section sliceLegs

variable (X : E)
variable [Limits.HasEnd (EndKan.End.endBifunctor (endConstProfunctor X))]

omit [Limits.HasEnd (EndKan.End.endBifunctor (endConstProfunctor X))] in
theorem endSliceCov_const (c d d' : OneCat) (f : d ⟶ d') :
    endSliceCov (endConstProfunctor X) c d d' f =
      𝟙 (endConstProfunctor X).obj (endWedge c d) := by
  dsimp [endSliceCov, endConstProfunctor, EndKan.End.endBifunctor]
  simp

omit [Limits.HasEnd (EndKan.End.endBifunctor (endConstProfunctor X))] in
theorem endSliceContrMap_const (c d d' : OneCat) (f : d ⟶ d') :
    endSliceContrMap (endConstProfunctor X) c d d' f =
      𝟙 (endConstProfunctor X).obj (endWedge c d') := by
  dsimp [endSliceContrMap, endConstProfunctor, EndKan.End.endBifunctor]
  simp

instance instAllEndSliceContrIso_const : AllEndSliceContrIso (endConstProfunctor X) :=
  allEndSliceContrIsoOfData (C := OneCat) (D := OneCat) (E := E) (F := endConstProfunctor X)
    fun c d d' f => by
      refine ⟨?_, ?_⟩
      · dsimp [endSliceCov, endConstProfunctor, EndKan.End.endBifunctor, endWedge]
        simp
        exact IsIso.id X
      · dsimp [endSliceContrMap, endConstProfunctor, EndKan.End.endBifunctor, endWedge]
        simp
        exact IsIso.id X

instance instEndSliceJointMono_const : EndSliceJointMono (endConstProfunctor X) where
  ext c d d' f u v h₁ _ := by
    dsimp [endSliceCov, endSliceContrMap, endConstProfunctor] at h₁ ⊢
    simp at h₁ ⊢
    exact h₁

end sliceLegs

section endFubiniCheck

variable (X : E)

variable [Limits.HasEnd (EndKan.End.endBifunctor (endConstProfunctor X))]
variable [∀ d, Limits.HasEnd (EndKan.End.endBifunctor (endSlice (endConstProfunctor X) d))]
variable [∀ d, Epi (endInnerLift (endConstProfunctor X) d)]
variable [Limits.HasEnd (EndKan.End.endBifunctor (endOuterProfunctor (endConstProfunctor X)))]

#check endFubiniIso (endConstProfunctor X)
#check endFubiniIso_hom (endConstProfunctor X)

end endFubiniCheck

end ConstantEnd

section ConstantCoend

variable {E : Type u} [Category.{v, u} E]

/-- Constant coend profunctor on `(OneCat × OneCat) × (OneCat × OneCat)ᵒᵖ`. -/
def coendConstProfunctor (X : E) : (OneCat × OneCat) × (OneCat × OneCat)ᵒᵖ ⥤ E where
  obj _ := X
  map _ := 𝟙 X
  map_id := by intro; simp
  map_comp := by intros; simp

section sliceLegs

variable (X : E) (c d d' : OneCat) (f : d ⟶ d')

theorem coendSliceCov_const :
    coendSliceCov (coendConstProfunctor X) c d d' f =
      𝟙 (coendConstProfunctor X).obj (coendWedge c d) := by
  dsimp [coendSliceCov, coendConstProfunctor]

theorem coendSliceContr_const :
    coendSliceContr (coendConstProfunctor X) c d d' f =
      𝟙 (coendConstProfunctor X).obj (coendWedge c d') := by
  dsimp [coendSliceContr, coendConstProfunctor]

theorem coendSliceMidToWedge_const :
    coendSliceMidToWedge (coendConstProfunctor X) c d d' f =
      𝟙 (coendConstProfunctor X).obj (coendMid c d d') := by
  dsimp [coendSliceMidToWedge, coendConstProfunctor]

instance instCoendSliceContrIso_const : CoendSliceContrIso (coendConstProfunctor X) :=
  coendSliceContrIsoOfData (C := OneCat) (D := OneCat) (E := E) (F := coendConstProfunctor X)
    (fun c d d' f => by
      refine ⟨?_, ?_⟩
      · dsimp [coendSliceCov, coendConstProfunctor, coendWedge]
        exact IsIso.id X
      · dsimp [coendSliceContr, coendConstProfunctor, coendWedge]
        exact IsIso.id X)
    (fun c d d' f => by
      dsimp [coendSliceMidToWedge, coendConstProfunctor, coendMid]
      exact inferInstanceAs (Epi (𝟙 X)))

instance instCoendSliceJointMono_const : CoendSliceJointMono (coendConstProfunctor X) where
  ext c d d' f u v h₁ _ := by
    dsimp [coendSliceCov, coendSliceContr, coendConstProfunctor] at h₁ ⊢
    simp at h₁ ⊢
    exact h₁

end sliceLegs

section coendFubiniCheck

variable (X : E)

variable [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendConstProfunctor X))]
variable [∀ d, Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice (coendConstProfunctor X) d))]
variable [∀ d, Mono (coendInnerDesc (coendConstProfunctor X) d)]
variable [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendOuterProfunctor (coendConstProfunctor X)))]

#check coendFubiniIso (coendConstProfunctor X)
#check coendFubiniIso_hom (coendConstProfunctor X)

end coendFubiniCheck

end ConstantCoend

end EndKan.Fubini.Examples
