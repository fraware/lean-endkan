import Mathlib.CategoryTheory.Limits.Shapes.End
import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Fubini.Slice
import EndKan.Fubini.CoendSlice
import EndKan.Fubini.Nested
import EndKan.Fubini.NestedCoend

namespace EndKan.Fubini

open CategoryTheory
open Opposite
open scoped Prod

universe u v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

/-!
### Fubini isomorphisms (extraction boundary)

The end Fubini isomorphism is

`EndKan.End.EndObj F ≅ endNestedObj F`,

proved as `endFubiniIso F` in `EndKan.Fubini.Nested`. Infrastructure in
`EndKan.Fubini.Slice`: `endSlice`, `endInnerObj`, `endInnerLift`, `endInnerMap`
(with `endInnerLift d ≫ endInnerMap f = endInnerLift d'`), and bootstrap isomorphisms
under `[AllEndSliceContrIso F]`. Indexing uses `EndIdx C D` (defeq to
`(C × D)ᵒᵖ × (C × D)`).

The coend mirror is `coendFubiniIso F : CoendObj F ≅ coendNestedObj F` in
`EndKan.Fubini.NestedCoend`, built from `coendSlice`, `coendInnerObj`, `coendInnerDesc`,
and `coendInnerMap` in `EndKan.Fubini.CoendSlice`. See `docs/EXTRACTION_LEDGER.md`.
-/

/-- Fubini isomorphism for ends over a product category. -/
def EndFubiniTarget (F : (C × D)ᵒᵖ × (C × D) ⥤ E)
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [∀ d, Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [AllEndSliceContrIso F]
    [∀ d, Epi (endInnerLift F d)]
    [Limits.HasEnd (EndKan.End.endBifunctor (endOuterProfunctor F))] : Prop :=
  Nonempty (EndKan.End.EndObj F ≅ endNestedObj F)

/-- Fubini isomorphism for coends over a product category. -/
def CoendFubiniTarget (F : (C × D) × (C × D)ᵒᵖ ⥤ E)
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [∀ d, Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [CoendSliceContrIso F]
    [∀ d, Mono (coendInnerDesc F d)]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendOuterProfunctor F))] : Prop :=
  Nonempty (EndKan.Coend.CoendObj F ≅ coendNestedObj F)

theorem end_fubini_target {F : (C × D)ᵒᵖ × (C × D) ⥤ E}
    [Limits.HasEnd (EndKan.End.endBifunctor F)]
    [∀ d, Limits.HasEnd (EndKan.End.endBifunctor (endSlice F d))]
    [AllEndSliceContrIso F]
    [∀ d, Epi (endInnerLift F d)]
    [Limits.HasEnd (EndKan.End.endBifunctor (endOuterProfunctor F))] :
    EndFubiniTarget F :=
  ⟨endFubiniIso F⟩

theorem coend_fubini_target {F : (C × D) × (C × D)ᵒᵖ ⥤ E}
    [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    [∀ d, Limits.HasCoend (EndKan.Coend.coendBifunctor (coendSlice F d))]
    [CoendSliceContrIso F]
    [∀ d, Mono (coendInnerDesc F d)]
    [Limits.HasCoend (EndKan.Coend.coendBifunctor (coendOuterProfunctor F))] :
    CoendFubiniTarget F :=
  ⟨coendFubiniIso F⟩

/-- β-reduction commutes with the universal morphisms used in Fubini diagrams. -/
theorem end_fubini_beta {F : Cᵒᵖ × C ⥤ E} [Limits.HasEnd (EndKan.End.endBifunctor F)] {X : E}
    (f : ∀ c : C, X ⟶ F.obj (op c, c))
    (h : ∀ {c c' : C} (g : c ⟶ c'),
      f c ≫ ((EndKan.End.endBifunctor F).obj (op c)).map g =
        f c' ≫ ((EndKan.End.endBifunctor F).map g.op).app c')
    (c : C) :
    EndKan.End.lift ⟨f, h⟩ ≫ EndKan.End.π F c = f c :=
  EndKan.End.end_beta f h c

/-- Product-diagonal end β (same as `end_fubini_beta` on `(C × D)`). -/
theorem end_fubini_π {F : (C × D)ᵒᵖ × (C × D) ⥤ E}
    [Limits.HasEnd (EndKan.End.endBifunctor F)] {X : E}
    (f : ∀ cd : C × D, X ⟶ F.obj (op cd, cd))
    (h : ∀ {cd cd' : C × D} (g : cd ⟶ cd'),
      f cd ≫ ((EndKan.End.endBifunctor F).obj (op cd)).map g =
        f cd' ≫ ((EndKan.End.endBifunctor F).map g.op).app cd')
    (cd : C × D) :
    EndKan.End.lift ⟨f, h⟩ ≫ EndKan.End.π F cd = f cd :=
  EndKan.End.end_beta f h cd

/-- β-reduction commutes with the universal morphisms used in Fubini diagrams. -/
theorem coend_fubini_beta {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (EndKan.Coend.coendBifunctor F)] {X : E}
    (f : ∀ c : C, F.obj (c, op c) ⟶ X)
    (h : ∀ {c c' : C} (g : c ⟶ c'),
      F.map (𝟙 c ×ₘ g.op) ≫ f c = F.map (g ×ₘ 𝟙 (op c')) ≫ f c')
    (c : C) :
    EndKan.Coend.ι F c ≫ EndKan.Coend.desc (EndKan.Coend.DinaturalTransformation.ofDiagonal f h) = f c :=
  EndKan.Coend.coend_beta f h c

/-- Curried coend β used in nested Fubini diagrams. -/
theorem coend_fubini_ιCurry_beta {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    {c c' : C} (f : c ⟶ c') :
    ((EndKan.Coend.coendBifunctor F).map f.op).app c ≫ EndKan.Coend.ιCurry F c =
      ((EndKan.Coend.coendBifunctor F).obj (op c')).map f ≫ EndKan.Coend.ιCurry F c' :=
  EndKan.Coend.coend_ιCurry_beta (F := F) f

/-- Diagonal coend injection β used in nested Fubini diagrams. -/
theorem coend_fubini_ι_beta {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (EndKan.Coend.coendBifunctor F)]
    {c c' : C} (f : c ⟶ c') :
    F.map (𝟙 c ×ₘ f.op) ≫ EndKan.Coend.ι F c = F.map (f ×ₘ 𝟙 (op c')) ≫ EndKan.Coend.ι F c' :=
  EndKan.Coend.coend_ι_beta (F := F) f

end EndKan.Fubini
