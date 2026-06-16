import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Opposites
import EndKan.Coend.Core
import EndKan.Coend.BetaEta

/-!
# Coend β/η examples (Mathlib extraction staging)

Buildable mirror of proposed `Mathlib.CategoryTheory.Limits.Shapes.Coend.Examples`.
Uses `EndKan.Coend` lemmas with abstract categories only — no tactics.

Staging docs: `scratch/mathlib-coend-beta/`. When porting to Mathlib, replace `EndKan.Coend`
names with `Limits.coendDiagonal` / `coendBifunctor` per `MODULE_STRUCTURE.md`.
-/

namespace Scratch.MathlibCoendBetaExamples

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Prod
open EndKan.Coend

universe u v

variable {C : Type u} [Category.{v} C] {E : Type u} [Category.{v} E]

/-- β-reduction: diagonal data factors through `ι` and the universal morphism. -/
theorem diagonal_beta (F : C × Cᵒᵖ ⥤ E) [HasCoend (coendBifunctor F)] {X : E}
    (f : ∀ c : C, F.obj (c, op c) ⟶ X)
    (h : ∀ {c c' : C} (g : c ⟶ c'),
      F.map (𝟙 c ×ₘ g.op) ≫ f c = F.map (g ×ₘ 𝟙 (op c')) ≫ f c')
    (c : C) :
    ι F c ≫ desc (DinaturalTransformation.ofDiagonal f h) = f c :=
  coend_beta f h c

/-- η-expansion: any morphism out of the coend is the universal morphism of its components along `ιCurry`. -/
theorem diagonal_eta (F : C × Cᵒᵖ ⥤ E) [HasCoend (coendBifunctor F)] {X : E}
    (f : CoendObj F ⟶ X) :
    f = desc {
      app := fun c => ιCurry F c ≫ f
      dinaturality := by
        intro c c' g
        rw [← Category.assoc, ιCurry_natural (F := F) g, Category.assoc] } :=
  coend_eta f

/-- Dinatural family packaged from diagonal data satisfies `desc_ιCurry`. -/
theorem diagonal_desc_ιCurry (F : C × Cᵒᵖ ⥤ E) [HasCoend (coendBifunctor F)] {X : E}
    (ω : DinaturalTransformation F X) (c : C) :
    ιCurry F c ≫ desc ω = ω.app c :=
  desc_ιCurry ω c

/-- Diagonal inclusions are dinatural (`F.map` form). -/
theorem diagonal_ι_dinatural (F : C × Cᵒᵖ ⥤ E) [HasCoend (coendBifunctor F)]
    {c c' : C} (g : c ⟶ c') :
    F.map (𝟙 c ×ₘ g.op) ≫ ι F c = F.map (g ×ₘ 𝟙 (op c')) ≫ ι F c' :=
  coend_ι_beta g

/-- Curried inclusions are dinatural (β for `ιCurry` itself). -/
theorem diagonal_ιCurry_dinatural (F : C × Cᵒᵖ ⥤ E) [HasCoend (coendBifunctor F)]
    {c c' : C} (g : c ⟶ c') :
    ((coendBifunctor F).map g.op).app c ≫ ιCurry F c =
      ((coendBifunctor F).obj (op c')).map g ≫ ιCurry F c' :=
  coend_ιCurry_beta g

/-- Functoriality along a profunctor transformation, via β for `map` and `ιCurry`. -/
theorem diagonal_map_ιCurry (F G : C × Cᵒᵖ ⥤ E) [HasCoend (coendBifunctor F)]
    [HasCoend (coendBifunctor G)] (α : F ⟶ G) (c : C) :
    ιCurry F c ≫ map α =
      ((coendNatTrans α).app (op c)).app c ≫ ιCurry G c :=
  coend_map_ιCurry α c

end Scratch.MathlibCoendBetaExamples
