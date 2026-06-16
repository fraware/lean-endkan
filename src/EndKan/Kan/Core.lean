import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta

namespace EndKan.Kan

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits

universe u v

variable {C D H : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} H]

/-- Pointwise left Kan extension (Mathlib-backed). -/
noncomputable abbrev Lan (K : C ⥤ D) (F : C ⥤ H)
    [HasPointwiseLeftKanExtension K F] : D ⥤ H :=
  pointwiseLeftKanExtension K F

/-- Pointwise right Kan extension (Mathlib-backed). -/
noncomputable abbrev Ran (K : C ⥤ D) (F : C ⥤ H)
    [HasPointwiseRightKanExtension K F] : D ⥤ H :=
  pointwiseRightKanExtension K F

/-- Helper: left Kan extensions are built from colimits of structured arrows. -/
theorem lan_obj_eq {K : C ⥤ D} {F : C ⥤ H} [HasPointwiseLeftKanExtension K F] (d : D) :
    (Lan K F).obj d = Limits.colimit (CostructuredArrow.proj K d ⋙ F) := by
  simp [Lan, pointwiseLeftKanExtension]

/-- Helper: right Kan extensions are built from limits of structured arrows. -/
theorem ran_obj_eq {K : C ⥤ D} {F : C ⥤ H} [HasPointwiseRightKanExtension K F] (d : D) :
    (Ran K F).obj d = Limits.limit (StructuredArrow.proj d K ⋙ F) := by
  simp [Ran, pointwiseRightKanExtension]
end EndKan.Kan
