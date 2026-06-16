import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.EpiMono

open CategoryTheory

variable {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)

#check IsIso
#print IsIso

example (h1 : f ≫ g = 𝟙 X) (h2 : g ≫ f = 𝟙 Y) : IsIso f := by
  exact ⟨Iso.mk f g h1 h2⟩
