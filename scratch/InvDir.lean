import Mathlib.CategoryTheory.Limits.Shapes.End
import EndKan.End.Core

open CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}

#check @CategoryTheory.inv
#check @CategoryTheory.IsIso.inv

example [IsIso f] : CategoryTheory.inv f ⟶ X := CategoryTheory.inv_comp_left f

example [IsIso f] : Y ⟶ CategoryTheory.inv f := CategoryTheory.comp_inv_right f
