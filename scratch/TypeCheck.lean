import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Opposites
import EndKan.End.Core
import EndKan.End.BetaEta

namespace Scratch.TypeCheck

open CategoryTheory
open CategoryTheory.Functor
open Opposite
open scoped Prod

universe u v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

abbrev EndIdx (C D : Type u) [Category C] [Category D] := Prod ((C × D)ᵒᵖ) (C × D)

abbrev endWedge (c : C) (d : D) : EndIdx C D := (op (c, d), c, d)

abbrev endOffCov (c : C) (d d' : D) : EndIdx C D := (op (c, d), c, d')

variable (F : EndIdx C D ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')
variable [Limits.HasEnd (EndKan.End.endBifunctor F)]

noncomputable def endSliceCov : F.obj (endWedge c d) ⟶ F.obj (endOffCov c d d') :=
  ((EndKan.End.endBifunctor F).obj (op (c, d))).map (𝟙 c ×ₘ f)

noncomputable def endSliceContrMap : F.obj (endWedge c d') ⟶ F.obj (endOffCov c d d') :=
  ((EndKan.End.endBifunctor F).map (𝟙 c ×ₘ f).op).app (c, d')

variable [IsIso (endSliceContrMap F c d d' f)]

#check (CategoryTheory.inv (endSliceContrMap F c d d' f) ≫ endSliceCov F c d d' f :
    F.obj (endOffCov c d d') ⟶ F.obj (endWedge c d))

end Scratch.TypeCheck
