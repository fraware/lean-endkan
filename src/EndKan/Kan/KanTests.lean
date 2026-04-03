import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Initial
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.Coequalizers
import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Kan.Core
import EndKan.Kan.BeckChevalley
import EndKan.Tactics

namespace EndKan.Tests.KanTests

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Test left Kan extension along fully faithful functors -/
theorem testLeftKanFullyFaithful (K : C ⥤ D) (F : C ⥤ E) (hK : Full K) (hK' : Faithful K) :
    Lan K F ≅ F := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension along fully faithful functors -/
theorem testRightKanFullyFaithful (K : C ⥤ D) (F : C ⥤ E) (hK : Full K) (hK' : Faithful K) :
    Ran K F ≅ F := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test density of Yoneda: Lan (yoneda) (evaluate F) reduces to F -/
theorem testDensityYoneda (F : C ⥤ D) :
    Lan (yoneda : C ⥤ Cᵒᵖ ⥤ Type*) (evaluate F) ≅ F := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test Beck-Chevalley on simple pullback square -/
theorem testBeckChevalleyPullback (K : C ⥤ D) (L : C ⥤ E) (M : D ⥤ F) (N : E ⥤ F)
    (S : BeckChevalley.Square K L M N) [h : BeckChevalley S] :
    M ⋙ Lan L (𝟙 E) ≅ Lan K (𝟙 D) ⋙ N := by
  endkan_beta
  endkan_eta
  kan_fuse
  beck_chevalley!
  simp

/-- Test left Kan extension along identity -/
theorem testLeftKanId (F : C ⥤ E) :
    Lan (𝟙 C) F ≅ F := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension along identity -/
theorem testRightKanId (F : C ⥤ E) :
    Ran (𝟙 C) F ≅ F := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test left Kan extension along composition -/
theorem testLeftKanComp (K : C ⥤ D) (L : D ⥤ E) (F : C ⥤ E) :
    Lan (K ⋙ L) F ≅ Lan L (Lan K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension along composition -/
theorem testRightKanComp (K : C ⥤ D) (L : D ⥤ E) (F : C ⥤ E) :
    Ran (K ⋙ L) F ≅ Ran L (Ran K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test left Kan extension preserves colimits -/
theorem testLeftKanPreservesColimits (K : C ⥤ D) (F : C ⥤ E) :
    PreservesColimits (Lan K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension preserves limits -/
theorem testRightKanPreservesLimits (K : C ⥤ D) (F : C ⥤ E) :
    PreservesLimits (Ran K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test left Kan extension preserves products -/
theorem testLeftKanPreservesProducts (K : C ⥤ D) (F : C ⥤ E) :
    PreservesLimitsOfShape (Discrete J) (Lan K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension preserves coproducts -/
theorem testRightKanPreservesCoproducts (K : C ⥤ D) (F : C ⥤ E) :
    PreservesColimitsOfShape (Discrete J) (Ran K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test left Kan extension preserves equalizers -/
theorem testLeftKanPreservesEqualizers (K : C ⥤ D) (F : C ⥤ E) :
    PreservesLimitsOfShape WalkingParallelPair (Lan K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension preserves coequalizers -/
theorem testRightKanPreservesCoequalizers (K : C ⥤ D) (F : C ⥤ E) :
    PreservesColimitsOfShape WalkingParallelPair (Ran K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test left Kan extension preserves pullbacks -/
theorem testLeftKanPreservesPullbacks (K : C ⥤ D) (F : C ⥤ E) :
    PreservesLimitsOfShape WalkingCospan (Lan K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension preserves pushouts -/
theorem testRightKanPreservesPushouts (K : C ⥤ D) (F : C ⥤ E) :
    PreservesColimitsOfShape WalkingSpan (Ran K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test left Kan extension preserves terminal objects -/
theorem testLeftKanPreservesTerminal (K : C ⥤ D) (F : C ⥤ E) :
    PreservesLimit (Functor.empty C) (Lan K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension preserves initial objects -/
theorem testRightKanPreservesInitial (K : C ⥤ D) (F : C ⥤ E) :
    PreservesColimit (Functor.empty C) (Ran K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test left Kan extension preserves binary products -/
theorem testLeftKanPreservesBinaryProducts (K : C ⥤ D) (F : C ⥤ E) :
    PreservesLimitsOfShape (Discrete WalkingPair) (Lan K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension preserves binary coproducts -/
theorem testRightKanPreservesBinaryCoproducts (K : C ⥤ D) (F : C ⥤ E) :
    PreservesColimitsOfShape (Discrete WalkingPair) (Ran K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test left Kan extension preserves finite products -/
theorem testLeftKanPreservesFiniteProducts (K : C ⥤ D) (F : C ⥤ E) :
    PreservesFiniteProducts (Lan K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension preserves finite coproducts -/
theorem testRightKanPreservesFiniteCoproducts (K : C ⥤ D) (F : C ⥤ E) :
    PreservesFiniteCoproducts (Ran K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test left Kan extension preserves filtered colimits -/
theorem testLeftKanPreservesFilteredColimits (K : C ⥤ D) (F : C ⥤ E) :
    PreservesFilteredColimits (Lan K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

/-- Test right Kan extension preserves sifted colimits -/
theorem testRightKanPreservesSiftedColimits (K : C ⥤ D) (F : C ⥤ E) :
    PreservesSiftedColimits (Ran K F) := by
  endkan_beta
  endkan_eta
  kan_fuse
  simp

end EndKan.Tests.KanTests
