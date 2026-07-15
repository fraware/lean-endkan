import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Opposites
import EndKan.Fubini

/-!
# Minimal `endBifunctor` consumer evidence

This file tests the narrowed Mathlib proposal against a real downstream consumer in
`EndKan.Fubini`. The candidate public surface contains one adapter and three general
normalization lemmas. Existing Mathlib end theorems provide the universal-property API.
-/

namespace Scratch.MathlibEndBifunctorConsumer

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open Opposite
open scoped Prod

universe u v

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {E : Type u} [Category.{v} E]

namespace Candidate

/-- Curried form of a profunctor `Cᵒᵖ × C ⥤ D`, as consumed by Mathlib's end API. -/
abbrev endBifunctor (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ ⥤ C ⥤ D :=
  curry.obj F

/-- General object normalization. The diagonal object lemma is a specialization. -/
@[simp]
theorem endBifunctor_fiber_obj {F : Cᵒᵖ × C ⥤ D} (c c' : C) :
    ((endBifunctor F).obj (op c)).obj c' = F.obj (op c, c') := by
  simp [endBifunctor]

/-- Covariant morphism normalization for the curried profunctor. -/
@[simp]
theorem endBifunctor_obj_map {F : Cᵒᵖ × C ⥤ D} (c : C) {c' c'' : C}
    (f : c' ⟶ c'') :
    ((endBifunctor F).obj (op c)).map f = F.map (𝟙 (op c) ×ₘ f) := by
  simp [endBifunctor]

/-- Contravariant morphism normalization for the curried profunctor. -/
@[simp]
theorem endBifunctor_map_app {F : Cᵒᵖ × C ⥤ D} {c c' : C} (f : c ⟶ c') :
    ((endBifunctor F).map f.op).app c' = F.map (f.op ×ₘ 𝟙 c') := by
  simp [endBifunctor]

/-- The diagonal object equation is derivable without another public declaration. -/
example {F : Cᵒᵖ × C ⥤ D} (c : C) :
    ((endBifunctor F).obj (op c)).obj c = F.obj (op c, c) := by
  simp

end Candidate

section ExistingConsumer

/-- Existing downstream theorem, retained as the baseline proof. -/
theorem fubini_beta_before {F : Cᵒᵖ × C ⥤ D}
    [HasEnd (EndKan.End.endBifunctor F)] {X : D}
    (f : ∀ c : C, X ⟶ F.obj (op c, c))
    (h : ∀ {c c' : C} (g : c ⟶ c'),
      f c ≫ ((EndKan.End.endBifunctor F).obj (op c)).map g =
        f c' ≫ ((EndKan.End.endBifunctor F).map g.op).app c')
    (c : C) :
    EndKan.End.lift ⟨f, h⟩ ≫ EndKan.End.π F c = f c :=
  EndKan.Fubini.end_fubini_beta f h c

end ExistingConsumer

section NarrowedConsumer

open Candidate

/-- The same β obligation uses the existing Mathlib theorem once the adapter is available. -/
theorem fubini_beta_after {F : Cᵒᵖ × C ⥤ D} [HasEnd (endBifunctor F)] {X : D}
    (f : ∀ c : C, X ⟶ F.obj (op c, c))
    (h : ∀ {c c' : C} (g : c ⟶ c'),
      f c ≫ ((endBifunctor F).obj (op c)).map g =
        f c' ≫ ((endBifunctor F).map g.op).app c')
    (c : C) :
    Limits.end_.lift (F := endBifunctor F) f (fun _ _ g => h g) ≫
        Limits.end_.π (endBifunctor F) c = f c := by
  exact Limits.end_.lift_π (F := endBifunctor F) f (fun _ _ g => h g) c

/-- The off-diagonal object rewrite in `EndKan.Fubini.Slice` is covered directly. -/
theorem fubini_slice_fiber (F : EndKan.Fubini.EndIdx C D ⥤ E) (cd cd' : C × D) :
    ((endBifunctor F).obj (op cd)).obj cd' = F.obj (op cd, cd') :=
  endBifunctor_fiber_obj cd cd'

/-- The covariant slice-map rewrite in `EndKan.Fubini.Slice` is covered directly. -/
theorem fubini_slice_obj_map (F : EndKan.Fubini.EndIdx C D ⥤ E) (cd : C × D)
    {cd' cd'' : C × D} (fg : cd' ⟶ cd'') :
    ((endBifunctor F).obj (op cd)).map fg = F.map (𝟙 (op cd) ×ₘ fg) :=
  endBifunctor_obj_map cd fg

/-- The contravariant slice-map rewrite in `EndKan.Fubini.Slice` is covered directly. -/
theorem fubini_slice_map_app (F : EndKan.Fubini.EndIdx C D ⥤ E)
    {cd cd' : C × D} (fg : cd ⟶ cd') :
    ((endBifunctor F).map fg.op).app cd' = F.map (fg.op ×ₘ 𝟙 cd') :=
  endBifunctor_map_app fg

end NarrowedConsumer

end Scratch.MathlibEndBifunctorConsumer
