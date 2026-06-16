import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Opposites
import EndKan.End.Core
import EndKan.End.BetaEta

/-!
# End β/η examples (Mathlib extraction staging)

Buildable mirror of proposed `Mathlib.CategoryTheory.Limits.Shapes.End.Examples`.
Uses `EndKan.End` lemmas with abstract categories only — no tactics.

Staging docs: `scratch/mathlib-end-beta/`. When porting to Mathlib, replace `EndKan.End`
names with `Limits.endDiagonal` / `endBifunctor` per `MODULE_STRUCTURE.md`.
-/

namespace Scratch.MathlibEndBetaExamples

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open EndKan.End

universe u v

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]

/-- β-reduction: a dinatural family into `F` factors through `π` at each object. -/
theorem diagonal_beta (F : Cᵒᵖ × C ⥤ D) [HasEnd (endBifunctor F)] {X : D}
    (ω : DinaturalTransformation X F) (c : C) :
    lift ω ≫ π F c = ω.app c :=
  end_beta (f := ω.app) (h := ω.dinaturality) c

/-- η-expansion: any morphism into the end is the lift of its components along `π`. -/
theorem diagonal_eta (F : Cᵒᵖ × C ⥤ D) [HasEnd (endBifunctor F)] {X : D}
    (f : X ⟶ EndObj F) :
    f = lift ⟨(fun c => f ≫ π F c), by
      intro c c' g
      simp only [Category.assoc, π_natural]⟩ :=
  end_eta f

/-- Projections are dinatural (β for `π` itself). -/
theorem diagonal_π_dinatural (F : Cᵒᵖ × C ⥤ D) [HasEnd (endBifunctor F)]
    {c c' : C} (g : c ⟶ c') :
    π F c ≫ ((endBifunctor F).obj (op c)).map g =
      π F c' ≫ ((endBifunctor F).map g.op).app c' :=
  end_π_beta g

/-- Functoriality along a profunctor transformation, via β for `map` and `π`. -/
theorem diagonal_map_π (F G : Cᵒᵖ × C ⥤ D) [HasEnd (endBifunctor F)]
    [HasEnd (endBifunctor G)] (α : F ⟶ G) (c : C) :
    map α ≫ π G c = π F c ≫ α.app (op c, c) :=
  end_map_beta α c

/-- Uniqueness of morphisms **out of** the end (Yoneda / covariant hom). -/
theorem diagonal_post_ext (F : Cᵒᵖ × C ⥤ D) [HasEnd (endBifunctor F)] {X : D}
    {f g : EndObj F ⟶ X}
    (h : ∀ (Y : D) (y : Y ⟶ EndObj F), y ≫ f = y ≫ g) : f = g :=
  post_ext h

end Scratch.MathlibEndBetaExamples
