import EndKan.Fubini
import EndKan.Fubini.Examples

/-!
# Fubini examples (Mathlib extraction staging)

Concrete nested Fubini on constant profunctors (`OneCat`). Demonstrates the
hypothesis-class consumer path documented in `scratch/mathlib-fubini/LEMMA_MAP.md`.

No tactics. When porting to Mathlib, replace `EndKan.Fubini` with
`Limits.endFubini` / `Limits.coendFubini` per `MODULE_STRUCTURE.md`.
-/

namespace Scratch.MathlibFubiniExamples

open CategoryTheory
open Opposite
open scoped Prod
open EndKan.Fubini
open EndKan.Fubini.Examples

universe u v

variable {E : Type u} [Category.{v, u} E]

section ConstantEnd

variable (X : E)

variable [Limits.HasEnd (EndKan.End.endBifunctor (endConstProfunctor X))]
variable [∀ d, Limits.HasEnd (EndKan.End.endBifunctor (endSlice (endConstProfunctor X) d))]
variable [∀ d, Epi (endInnerLift (endConstProfunctor X) d)]
variable [Limits.HasEnd (EndKan.End.endBifunctor (endOuterProfunctor (endConstProfunctor X)))]

/-- Nested end Fubini for a constant profunctor: `EndObj F ≅ endNestedObj F`. -/
noncomputable def constant_end_fubini_iso :
    EndKan.End.EndObj (endConstProfunctor X) ≅ endNestedObj (endConstProfunctor X) :=
  endFubiniIso (endConstProfunctor X)

/-- Target packaging: nested end Fubini holds for constant profunctors. -/
theorem constant_end_fubini_target : EndFubiniTarget (endConstProfunctor X) :=
  end_fubini_target (F := endConstProfunctor X)

end ConstantEnd

section ConstantCoend

variable (X : E)

variable [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendConstProfunctor X))]
variable [∀ d, Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice (coendConstProfunctor X) d))]
variable [∀ d, Mono (coendInnerDesc (coendConstProfunctor X) d)]
variable [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendOuterProfunctor (coendConstProfunctor X)))]

/-- Nested coend Fubini for a constant profunctor. -/
noncomputable def constant_coend_fubini_iso :
    EndKan.Coend.CoendObj (coendConstProfunctor X) ≅ coendNestedObj (coendConstProfunctor X) :=
  coendFubiniIso (coendConstProfunctor X)

theorem constant_coend_fubini_target : CoendFubiniTarget (coendConstProfunctor X) :=
  coend_fubini_target (F := coendConstProfunctor X)

end ConstantCoend

end Scratch.MathlibFubiniExamples
