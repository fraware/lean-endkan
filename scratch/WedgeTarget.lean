import EndKan.Fubini.Slice

open CategoryTheory EndKan.Fubini

universe u v
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable (F : EndIdx C D ⥤ E) (c : C) (d d' : D) (f : d ⟶ d')
variable [Limits.HasEnd (EndKan.End.endBifunctor F)]
variable [AllEndSliceContrIso F]

#check (endSliceCov F c d d' f : F.obj (endWedge c d) ⟶ F.obj (endOffCov c d d'))
#check (endSliceContrMap F c d d' f : F.obj (endWedge c d') ⟶ F.obj (endOffCov c d d'))
#check (endSliceOpCovIso F c d d' f : F.obj (endWedge c d) ⟶ F.obj (endWedge c d'))
#check (endSliceOpCovIso F c d d' f : F.obj (endWedge c d) ⟶ F.obj (endWedge c d'))
