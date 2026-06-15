import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Products.Basic
import EndKan.End.Core

open CategoryTheory

variable {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)

#check @CategoryTheory.IsIso.mk
#check @CategoryTheory.IsIso.mk'

example (h1 : f ≫ g = 𝟙 X) (h2 : g ≫ f = 𝟙 Y) : IsIso f :=
  IsIso.mk ⟨g, h1, h2⟩

example (h1 : g ≫ f = 𝟙 Y) (h2 : f ≫ g = 𝟙 X) : IsIso f :=
  IsIso.mk' g h1 h2
