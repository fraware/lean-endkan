import EndKan.Fubini.Slice

open CategoryTheory EndKan.Fubini

universe u v
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable (F : EndIdx C D ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')
variable [Limits.HasEnd (EndKan.End.endBifunctor F)]
variable [AllEndSliceContrIso F]
variable [IsIso (endSliceCov F c d d' f)]

#check endSliceInvContr F c d d' f
#check (endSliceContrMap F c d d' f ≫ endSliceInvContr F c d d' f)
#check (𝟙 (F.obj (endWedge c d')))
