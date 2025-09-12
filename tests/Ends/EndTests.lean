import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Tactics

namespace EndKan.Tests.EndTests

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- Test naturality via ends using β/η transformations -/
theorem testNaturalityViaEnds (F : Cᵒᵖ × C ⥤ D) (G : Cᵒᵖ × C ⥤ D) (α : F ⟶ G) :
    End.map α ≫ End.π G c = End.π F c ≫ α.app (op c, c) := by
  end_beta
  end_eta
  simp

/-- Test Fubini's theorem: End of End reduces to iterated end -/
theorem testFubiniEnds (F : (C × D)ᵒᵖ × (C × D) ⥤ E) [HasProductsOfShape C E] [HasProductsOfShape D E] :
    EndObj F ≅ EndObj (fun c => EndObj (fun d => F.obj (op (c, d), (c, d)))) := by
  endkan_beta
  endkan_eta
  simp

/-- Test end β transformation for standard presentations -/
theorem testEndBeta (F : Cᵒᵖ × C ⥤ D) (X : D) (f : ∀ c : C, X ⟶ F.obj (op c, c))
    (h : ∀ {c c' : C} (g : c ⟶ c'), f c ≫ F.map (op g, g) = f c') (c : C) :
    End.lift f h ≫ End.π F c = f c := by
  end_beta

/-- Test end η transformation for uniqueness -/
theorem testEndEta (F : Cᵒᵖ × C ⥤ D) (X : D) (f : X ⟶ EndObj F) :
    f = End.lift (fun c => f ≫ End.π F c) (by
      intro c c' g
      simp only [Category.assoc, End.π_natural]) := by
  end_eta

/-- Test end map composition -/
theorem testEndMapComp (F G H : Cᵒᵖ × C ⥤ D) (α : F ⟶ G) (β : G ⟶ H) :
    End.map α ≫ End.map β = End.map (α ≫ β) := by
  endkan_beta
  endkan_eta
  simp

/-- Test end map identity -/
theorem testEndMapId (F : Cᵒᵖ × C ⥤ D) :
    End.map (𝟙 F) = 𝟙 (EndObj F) := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of constant functor -/
theorem testEndConst (X : D) :
    EndObj (Functor.const (Cᵒᵖ × C) X) ≅ X := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of representable functor -/
theorem testEndRepresentable (c : C) :
    EndObj (yoneda.obj c) ≅ 𝟙_ C := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of product functor -/
theorem testEndProduct (F G : Cᵒᵖ × C ⥤ D) [HasBinaryProducts D] :
    EndObj (F.prod G) ≅ EndObj F × EndObj G := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of functor composition -/
theorem testEndComp (F : Cᵒᵖ × C ⥤ D) (H : D ⥤ E) :
    EndObj (F ⋙ H) ≅ H.obj (EndObj F) := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of opposite functor -/
theorem testEndOp (F : Cᵒᵖ × C ⥤ D) :
    EndObj (F.op) ≅ (EndObj F).op := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of functor category -/
theorem testEndFunctor (F : (C ⥤ D)ᵒᵖ × (C ⥤ D) ⥤ E) [HasProductsOfShape (C ⥤ D) E] :
    EndObj F ≅ EndObj (fun F' => EndObj (fun c => F.obj (op F', F') c)) := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of limit functor -/
theorem testEndLimit (F : Cᵒᵖ × C ⥤ D) [HasLimitsOfShape J D] :
    EndObj (F ⋙ lim) ≅ lim.obj (EndObj F) := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of colimit functor -/
theorem testEndColimit (F : Cᵒᵖ × C ⥤ D) [HasColimitsOfShape J D] :
    EndObj (F ⋙ colim) ≅ colim.obj (EndObj F) := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of terminal functor -/
theorem testEndTerminal (F : Cᵒᵖ × C ⥤ D) [HasTerminal D] :
    EndObj (F ⋙ (Functor.const D (𝟙_ D))) ≅ 𝟙_ D := by
  endkan_beta
  endkan_eta
  simp

/-- Test end of initial functor -/
theorem testEndInitial (F : Cᵒᵖ × C ⥤ D) [HasInitial D] :
    EndObj (F ⋙ (Functor.const D (⊥_ D))) ≅ ⊥_ D := by
  endkan_beta
  endkan_eta
  simp

end EndKan.Tests.EndTests
