import EndKan.Kan.BeckChevalley
import EndKan.Kan.BeckChevalley.Hypotheses

/-!
# Kan / Beck–Chevalley examples (Mathlib extraction staging)

Abstract smoke tests for the comparison API under equivalence hypotheses.
No tactics.

Staging: `scratch/mathlib-kan-bc/`, `docs/MATHLIB_PR_KAN_BECKCHEVALLEY.md`.
-/

namespace Scratch.MathlibKanBcExamples

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open EndKan.Kan
open EndKan.Kan.BeckChevalley

universe u v

variable {C D E B : Type u} [Category.{v, u} C] [Category.{v, u} D] [Category.{v, u} E]
    [Category.{v, u} B]
variable {H : Type u} [Category.{v, u} H]
variable (K : C ⥤ D) (M : D ⥤ B) [IsEquivalence K]

/-- Reflexive square carries a Beck–Chevalley instance when `K` is an equivalence. -/
theorem refl_square_beck_chevalley : BeckChevalley (reflSquare K M) :=
  inferInstance

/-- Comparison morphism is an isomorphism on the reflexive square. -/
theorem refl_square_compare_iso (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (K ⋙ M ⋙ F)] :
    IsIso (beckChevalleyCompare (reflSquare K M) F) :=
  beckChevalleyIso (reflSquare K M) F

section SquareComm

variable {K : C ⥤ D} {M : D ⥤ B}

/-- South leg of the comma square matches whiskering the commutative datum. -/
theorem square_comm_whisker_example (L : C ⥤ E) (N : E ⥤ B) (S : Square K L M N) (F : B ⥤ H) :
    L ⋙ N ⋙ F = K ⋙ M ⋙ F :=
  square_comm_whisker S F

end SquareComm

end Scratch.MathlibKanBcExamples
