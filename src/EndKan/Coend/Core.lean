import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EqToHom

namespace EndKan.Coend

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Prod
open Opposite
open scoped Prod

universe u v

variable {C : Type u} [Category.{v} C] {E : Type u} [Category.{v} E]

/-- Swap a functor `C × Cᵒᵖ ⥤ E` into `Cᵒᵖ × C ⥤ E`. -/
abbrev coendSwap (F : C × Cᵒᵖ ⥤ E) : Cᵒᵖ × C ⥤ E :=
  CategoryTheory.Prod.swap Cᵒᵖ C ⋙ F

/-- The curried form of a functor `C × Cᵒᵖ ⥤ E`, as used by Mathlib's `coend`. -/
abbrev coendBifunctor (F : C × Cᵒᵖ ⥤ E) : Cᵒᵖ ⥤ C ⥤ E :=
  curry.obj (coendSwap F)

@[simp]
theorem coendDiagonal {F : C × Cᵒᵖ ⥤ E} (c : C) :
    ((coendBifunctor F).obj (op c)).obj c = F.obj (c, op c) := by
  simp [coendBifunctor, coendSwap, curryObj, Functor.comp_obj, swap_obj]

@[simp]
theorem coendDiagonal_app {F : C × Cᵒᵖ ⥤ E} {c c' : C} :
    ((coendBifunctor F).obj (op c')).obj c = F.obj (c, op c') := by
  simp [coendBifunctor, coendSwap, curryObj, Functor.comp_obj, swap_obj]

@[simp]
theorem coendBifunctor_map_app {F : C × Cᵒᵖ ⥤ E} {c c' : C} (f : c ⟶ c') :
    ((coendBifunctor F).map f.op).app c = F.map (𝟙 c ×ₘ f.op) := by
  dsimp [coendBifunctor, coendSwap, curryObj, Functor.comp_obj, swap_obj]
  rfl

@[simp]
theorem coendBifunctor_obj_map {F : C × Cᵒᵖ ⥤ E} {c c' : C} (f : c ⟶ c') :
    ((coendBifunctor F).obj (op c')).map f = F.map (f ×ₘ 𝟙 (op c')) := by
  dsimp [coendBifunctor, coendSwap, curryObj, Functor.comp_obj, swap_obj]
  rfl

/-- A natural transformation on swapped arguments, for use with `coendBifunctor`. -/
def coendNatTrans {F G : C × Cᵒᵖ ⥤ E} (α : F ⟶ G) :
    coendBifunctor F ⟶ coendBifunctor G :=
  curry.map (whiskerLeft (CategoryTheory.Prod.swap Cᵒᵖ C) α)

/-- A dinatural transformation from `F` into `X`, in curried form. -/
structure DinaturalTransformation (F : C × Cᵒᵖ ⥤ E) (X : E) where
  app : ∀ c : C, ((coendBifunctor F).obj (op c)).obj c ⟶ X
  dinaturality : ∀ ⦃c c' : C⦄ (f : c ⟶ c'),
    ((coendBifunctor F).map f.op).app c ≫ app c =
      ((coendBifunctor F).obj (op c')).map f ≫ app c'

@[simp]
lemma eqToHom_symm_comp_mpr_diagonal {F : C × Cᵒᵖ ⥤ E} {c : C} {X : E}
    (f : F.obj (c, op c) ⟶ X) :
    eqToHom (coendDiagonal (F := F) c).symm ≫
      (congrArg (fun W => W ⟶ X) (coendDiagonal (F := F) c)).mpr f = f := by
  have p := coendDiagonal (F := F) c
  have h₁ := congrArg_mpr_hom_left p f
  have h₂ : eqToHom p.symm ≫ eqToHom p = 𝟙 _ := by
    simpa [eqToIso.inv, eqToIso.hom] using (eqToIso p).inv_hom_id
  calc
    eqToHom p.symm ≫ (congrArg (fun W => W ⟶ X) p).mpr f
        = eqToHom p.symm ≫ eqToHom p ≫ f := by rw [h₁]
    _ = f := by rw [← Category.assoc, h₂, Category.id_comp]

/-- `congrArg`/`mpr` form of the diagonal inclusion (for rewrites on hom-types). -/
lemma mpr_hom_ιCurry {F : C × Cᵒᵖ ⥤ E} {c : C} {X : E}
    (f : ((coendBifunctor F).obj (op c)).obj c ⟶ X) :
    (congrArg (fun W => W ⟶ X) (coendDiagonal (F := F) c).symm).mpr f =
      eqToHom (coendDiagonal (F := F) c).symm ≫ f :=
  congrArg_mpr_hom_left _ _

/-- Build a dinatural transformation from diagonal data in `C × Cᵒᵖ`. -/
def DinaturalTransformation.ofDiagonal {F : C × Cᵒᵖ ⥤ E} {X : E}
    (f : ∀ c : C, F.obj (c, op c) ⟶ X)
    (h : ∀ {c c' : C} (g : c ⟶ c'),
      F.map (𝟙 c ×ₘ g.op) ≫ f c = F.map (g ×ₘ 𝟙 (op c')) ≫ f c') :
    DinaturalTransformation F X where
  app c := (congrArg (fun W => W ⟶ X) (coendDiagonal (F := F) c)).mpr (f c)
  dinaturality := by
    intro c c' g
    simp only [congrArg_mpr_hom_left, coendBifunctor_map_app, coendBifunctor_obj_map, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact h (g := g)

/-- The coend of `F`, defined via Mathlib's `CategoryTheory.Limits.coend`. -/
noncomputable abbrev CoendObj (F : C × Cᵒᵖ ⥤ E) [Limits.HasCoend (coendBifunctor F)] : E :=
  Limits.coend (coendBifunctor F)

/-- Curried inclusion into the coend. -/
noncomputable abbrev ιCurry (F : C × Cᵒᵖ ⥤ E) [Limits.HasCoend (coendBifunctor F)] (c : C) :
    ((coendBifunctor F).obj (op c)).obj c ⟶ CoendObj F :=
  Limits.coend.ι (coendBifunctor F) c

/-- Inclusion from the diagonal object `F(c, c)` into the coend. -/
noncomputable def ι (F : C × Cᵒᵖ ⥤ E) [Limits.HasCoend (coendBifunctor F)] (c : C) :
    F.obj (c, op c) ⟶ CoendObj F :=
  eqToHom (coendDiagonal (F := F) c).symm ≫ ιCurry F c

@[simp]
theorem ι_eq {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)] (c : C) :
    ι F c = eqToHom (coendDiagonal (F := F) c).symm ≫ ιCurry F c := rfl

/-- The coend inclusions form a dinatural transformation. -/
noncomputable def dinatural (F : C × Cᵒᵖ ⥤ E) [Limits.HasCoend (coendBifunctor F)] :
    DinaturalTransformation F (CoendObj F) where
  app := ιCurry F
  dinaturality := fun _ _ f => Limits.coend.condition (coendBifunctor F) f

/-- Universal property of coends. -/
noncomputable abbrev desc {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)]
    {X : E} (ω : DinaturalTransformation F X) : CoendObj F ⟶ X :=
  Limits.coend.desc ω.app (fun ⦃i j : C⦄ (g : i ⟶ j) => ω.dinaturality (f := g))

@[reassoc (attr := simp)]
theorem desc_ιCurry {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)]
    {X : E} (ω : DinaturalTransformation F X) (c : C) :
    ιCurry F c ≫ desc ω = ω.app c :=
  Limits.coend.ι_desc ω.app (fun ⦃i j : C⦄ (g : i ⟶ j) => ω.dinaturality (f := g)) c

@[reassoc (attr := simp)]
theorem desc_ι {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)]
    {X : E} (ω : DinaturalTransformation F X) (c : C) :
    ι F c ≫ desc ω = eqToHom (coendDiagonal (F := F) c).symm ≫ ω.app c := by
  rw [ι, Category.assoc, desc_ιCurry]

theorem uniq {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)]
    {X : E} (f g : CoendObj F ⟶ X)
    (h : ∀ c : C, ιCurry F c ≫ f = ιCurry F c ≫ g) : f = g :=
  Limits.coend.hom_ext (f := f) (g := g) h

@[reassoc (attr := simp)]
theorem ιCurry_natural {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)]
    {c c' : C} (f : c ⟶ c') :
    ((coendBifunctor F).map f.op).app c ≫ ιCurry F c =
      ((coendBifunctor F).obj (op c')).map f ≫ ιCurry F c' :=
  Limits.coend.condition (coendBifunctor F) f

/-- Diagonal dinaturality of the coend inclusion. -/
@[reassoc (attr := simp)]
theorem ι_dinatural {F : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)]
    {c c' : C} (f : c ⟶ c') :
    F.map (𝟙 c ×ₘ f.op) ≫ ι F c = F.map (f ×ₘ 𝟙 (op c')) ≫ ι F c' := by
  rw [ι, ι, ← coendBifunctor_map_app, ← coendBifunctor_obj_map]
  convert Limits.coend.condition (coendBifunctor F) f using 1
  · rw [← Category.assoc]
    exact HEq.eq <|
      heq_comp (eq1 := rfl) (eq2 := coendDiagonal (F := F) c) (eq3 := rfl)
        (H1 := comp_eqToHom_heq (f := ((coendBifunctor F).map f.op).app c)
          (h := (coendDiagonal (F := F) c).symm))
        HEq.rfl
  · rw [← Category.assoc]
    exact HEq.eq <|
      heq_comp (eq1 := rfl) (eq2 := coendDiagonal (F := F) c') (eq3 := rfl)
        (H1 := comp_eqToHom_heq (f := ((coendBifunctor F).obj (op c')).map f)
          (h := (coendDiagonal (F := F) c').symm))
        HEq.rfl

/-- A natural transformation induces a morphism between coends. -/
noncomputable abbrev map {F G : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)]
    [Limits.HasCoend (coendBifunctor G)] (α : F ⟶ G) : CoendObj F ⟶ CoendObj G :=
  Limits.coend.map (coendNatTrans α)

@[reassoc (attr := simp)]
theorem map_ιCurry {F G : C × Cᵒᵖ ⥤ E} [Limits.HasCoend (coendBifunctor F)]
    [Limits.HasCoend (coendBifunctor G)] (α : F ⟶ G) (c : C) :
    ιCurry F c ≫ map α =
      ((coendNatTrans α).app (op c)).app c ≫ ιCurry G c :=
  Limits.coend.ι_map (coendNatTrans α) c

end EndKan.Coend
