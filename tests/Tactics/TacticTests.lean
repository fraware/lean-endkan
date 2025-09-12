import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.HasColimits
import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Kan.Core
import EndKan.Kan.BeckChevalley
import EndKan.Tactics
import EndKan.Transformation
import EndKan.ErrorHandling

namespace EndKan.TacticTests

open CategoryTheory
open CategoryTheory.Limits
open EndKan.Tactics
open EndKan.Transformation
open EndKan.ErrorHandling

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Test basic end β-reduction -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  end_beta

/-- Test basic end η-expansion -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : D.obj (op c, c) ⟶ EndObj F) :
  f = End.lift (fun c => f ≫ End.π F c) (by
    intro c c' g
    simp only [Category.assoc, End.π_natural]) := by
  end_eta

/-- Test basic coend β-reduction -/
example (F : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D]
        (f : ∀ c : C, F.obj (c, op c) ⟶ D.obj (c, op c)) (h : ∀ {c c' : C} (g : c ⟶ c'), F.map (g, op g) ≫ f c' = f c) (c : C) :
  Coend.ι F c ≫ Coend.desc f h = f c := by
  coend_beta

/-- Test basic coend η-expansion -/
example (F : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D]
        (f : CoendObj F ⟶ D.obj (c, op c)) :
  f = Coend.desc (fun c => Coend.ι F c ≫ f) (by
    intro c c' g
    simp only [Category.assoc, Coend.ι_natural]) := by
  coend_eta

/-- Test Kan extension fusion -/
example (K : C ⥤ D) (F : C ⥤ E) [HasCoproductsOfShape C E] [HasWideCoequalizers E]
        (hK : Full K) (hK' : Faithful K) :
  Lan K F ≅ F := by
  kan_fuse

/-- Test Beck-Chevalley -/
example (K : C ⥤ D) (L : C ⥤ E) (M : D ⥤ F) (N : E ⥤ F)
        (S : BeckChevalley.Square K L M N) [BeckChevalley S] :
  M ⋙ Lan L (𝟙 E) ≅ Lan K (𝟙 D) ⋙ N := by
  beck_chevalley!

/-- Test combined tactics -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (G : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D] :
  EndObj F ≅ EndObj F ∧ CoendObj G ≅ CoendObj G := by
  constructor
  · endkan_beta
  · endkan_eta

/-- Test smart tactic -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  endkan_smart

/-- Test debug tactic -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  endkan_debug

/-- Test enhanced tactics with error handling -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  end_beta!

/-- Test timeout handling -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  setTimeout 1000
  end_beta!

/-- Test tracing -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  setTrace true
  end_beta!

/-- Test debug mode -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  setDebug true
  end_beta!

/-- Test aggressive mode -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  setAggressive true
  end_beta!

/-- Test max steps -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  setMaxSteps 50
  end_beta!

/-- Test pattern matching for different goal types -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (G : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D]
        (K : C ⥤ D) (L : C ⥤ E) (M : D ⥤ F) (N : E ⥤ F) :
  EndObj F ≅ EndObj F ∧
  CoendObj G ≅ CoendObj G ∧
  Lan K (𝟙 C) ≅ 𝟙 C ∧
  Ran K (𝟙 C) ≅ 𝟙 C := by
  constructor
  · endkan_smart
  · endkan_smart
  · endkan_smart
  · endkan_smart

/-- Test error recovery -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  try
    end_beta!
  catch e =>
    logError s!"EndKan error: {e.message}"
    simp

/-- Test term mode tactics -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (f : ∀ c : C, D.obj (op c, c)) (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
  End.lift f h ≫ End.π F c = f c := by
  exact by end_beta

/-- Test complex nested expressions -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (G : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D]
        (H : D ⥤ E) [HasProductsOfShape C E] [HasWideEqualizers E]
        [HasCoproductsOfShape C E] [HasWideCoequalizers E] :
  H.obj (EndObj F) ≅ EndObj (F ⋙ H) ∧
  H.obj (CoendObj G) ≅ CoendObj (G ⋙ H) := by
  constructor
  · endkan_smart
  · endkan_smart

/-- Test performance with large expressions -/
example (F : Cᵒᵖ × C ⥤ D) [HasProductsOfShape C D] [HasWideEqualizers D]
        (G : C × Cᵒᵖ ⥤ D) [HasCoproductsOfShape C D] [HasWideCoequalizers D]
        (H : D ⥤ E) [HasProductsOfShape C E] [HasWideEqualizers E]
        [HasCoproductsOfShape C E] [HasWideCoequalizers E]
        (I : E ⥤ F) [HasProductsOfShape C F] [HasWideEqualizers F]
        [HasCoproductsOfShape C F] [HasWideCoequalizers F] :
  (H ⋙ I).obj (EndObj F) ≅ EndObj (F ⋙ H ⋙ I) ∧
  (H ⋙ I).obj (CoendObj G) ≅ CoendObj (G ⋙ H ⋙ I) := by
  constructor
  · endkan_smart
  · endkan_smart

end EndKan.TacticTests
