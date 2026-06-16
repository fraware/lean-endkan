import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Fubini
import EndKan.Fubini.Examples
import EndKan.Kan.BeckChevalley
import EndKan.Kan.BeckChevalley.Hypotheses

/-!
Compile-time fixtures: well-typed statements of the public β/η and extraction API.
-/

namespace EndKan.TestFixtures

open CategoryTheory
open CategoryTheory.Functor
open Opposite
open scoped Prod

section Abstract

universe u v

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D] {E : Type u} [Category.{v} E]
variable (F : Cᵒᵖ × C ⥤ D) [Limits.HasEnd (EndKan.End.endBifunctor F)]
variable (G : C × Cᵒᵖ ⥤ E) [Limits.HasCoend (EndKan.Coend.coendBifunctor G)]

#check @EndKan.End.end_beta
#check @EndKan.End.end_eta
#check @EndKan.End.end_π_beta

#check @EndKan.Coend.coend_beta
#check @EndKan.Coend.coend_eta
#check @EndKan.Coend.coend_ιCurry_beta

end Abstract

section Fubini

universe u v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable (F : (C × D)ᵒᵖ × (C × D) ⥤ E)
variable (G : (C × D) × (C × D)ᵒᵖ ⥤ E)

#check @EndKan.Fubini.endFubiniIso
#check @EndKan.Fubini.coendFubiniIso
#check @EndKan.Fubini.endFubiniIso_hom
#check @EndKan.Fubini.coendFubiniIso_hom

section ConcreteFubiniExamples

open EndKan.Fubini
open EndKan.Fubini.Examples

variable {E : Type u} [Category.{v, u} E] (X : E)

variable [Limits.HasEnd (EndKan.End.endBifunctor (endConstProfunctor X))]
variable [∀ d, Limits.HasEnd (EndKan.End.endBifunctor (endSlice (endConstProfunctor X) d))]
variable [∀ d, Epi (endInnerLift (endConstProfunctor X) d)]
variable [Limits.HasEnd (EndKan.End.endBifunctor (endOuterProfunctor (endConstProfunctor X)))]
variable [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendConstProfunctor X))]
variable [∀ d, Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice (coendConstProfunctor X) d))]
variable [∀ d, Mono (coendInnerDesc (coendConstProfunctor X) d)]
variable [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendOuterProfunctor (coendConstProfunctor X)))]

#check endFubiniIso (endConstProfunctor X)
#check coendFubiniIso (coendConstProfunctor X)

end ConcreteFubiniExamples

end Fubini

section BeckChevalley

universe u v

variable {C D B : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} B]
variable (K : C ⥤ D) (M : D ⥤ B) [IsEquivalence K]

#check (inferInstance : EndKan.Kan.BeckChevalley.BeckChevalley
  (EndKan.Kan.BeckChevalley.reflSquare (K := K) (M := M)))
#check @EndKan.Kan.BeckChevalley.beckChevalleyCompare
#check @EndKan.Kan.BeckChevalley.beckChevalleyIso

end BeckChevalley

end EndKan.TestFixtures
