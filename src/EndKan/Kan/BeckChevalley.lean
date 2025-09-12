import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import EndKan.Kan.Core

namespace EndKan.Kan.BeckChevalley

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E] {F : Type*} [Category F]

/-- A commutative square of functors -/
structure Square (K : C ⥤ D) (L : C ⥤ E) (M : D ⥤ F) (N : E ⥤ F) where
  comm : K ⋙ M = L ⋙ N

/-- Beck-Chevalley condition for a square -/
class BeckChevalley (S : Square K L M N) where
  isPullback : IsPullback S.comm
  isFullyFaithful : Full K ∧ Faithful K
  isExact : Exact K L

/-- Beck-Chevalley isomorphism -/
def beckChevalleyIso {S : Square K L M N} [h : BeckChevalley S] :
    M ⋙ Lan L (𝟙 E) ≅ Lan K (𝟙 D) ⋙ N :=
  { hom := Lan.universal (Lan.universal (𝟙 E))
    inv := Lan.universal (Lan.universal (𝟙 D))
    hom_inv_id := by simp
    inv_hom_id := by simp }

/-- Beck-Chevalley condition for pullback squares -/
def beckChevalleyPullback {S : Square K L M N} (h : IsPullback S.comm) :
    BeckChevalley S where
  isPullback := h
  isFullyFaithful := ⟨Full.id, Faithful.id⟩
  isExact := Exact.id

/-- Beck-Chevalley condition for fully faithful functors -/
def beckChevalleyFullyFaithful {S : Square K L M N} (hK : Full K) (hK' : Faithful K) :
    BeckChevalley S where
  isPullback := IsPullback.id
  isFullyFaithful := ⟨hK, hK'⟩
  isExact := Exact.id

/-- Beck-Chevalley condition for exact functors -/
def beckChevalleyExact {S : Square K L M N} (h : Exact K L) :
    BeckChevalley S where
  isPullback := IsPullback.id
  isFullyFaithful := ⟨Full.id, Faithful.id⟩
  isExact := h

/-- Beck-Chevalley condition for identity squares -/
def beckChevalleyId (K : C ⥤ D) : BeckChevalley (Square.mk (by simp)) where
  isPullback := IsPullback.id
  isFullyFaithful := ⟨Full.id, Faithful.id⟩
  isExact := Exact.id

/-- Beck-Chevalley condition for composition of squares -/
def beckChevalleyComp {S₁ : Square K L M N} {S₂ : Square M N P Q}
    [h₁ : BeckChevalley S₁] [h₂ : BeckChevalley S₂] :
    BeckChevalley (Square.mk (by simp [S₁.comm, S₂.comm])) where
  isPullback := IsPullback.comp h₁.isPullback h₂.isPullback
  isFullyFaithful := ⟨Full.comp h₁.isFullyFaithful.1 h₂.isFullyFaithful.1,
                      Faithful.comp h₁.isFullyFaithful.2 h₂.isFullyFaithful.2⟩
  isExact := Exact.comp h₁.isExact h₂.isExact

/-- Beck-Chevalley condition for opposite squares -/
def beckChevalleyOp {S : Square K L M N} [h : BeckChevalley S] :
    BeckChevalley (Square.mk (by simp [S.comm])) where
  isPullback := IsPullback.op h.isPullback
  isFullyFaithful := ⟨Full.op h.isFullyFaithful.1, Faithful.op h.isFullyFaithful.2⟩
  isExact := Exact.op h.isExact

/-- Beck-Chevalley condition for product squares -/
def beckChevalleyProd {S₁ : Square K₁ L₁ M₁ N₁} {S₂ : Square K₂ L₂ M₂ N₂}
    [h₁ : BeckChevalley S₁] [h₂ : BeckChevalley S₂] :
    BeckChevalley (Square.mk (by simp [S₁.comm, S₂.comm])) where
  isPullback := IsPullback.prod h₁.isPullback h₂.isPullback
  isFullyFaithful := ⟨Full.prod h₁.isFullyFaithful.1 h₂.isFullyFaithful.1,
                      Faithful.prod h₁.isFullyFaithful.2 h₂.isFullyFaithful.2⟩
  isExact := Exact.prod h₁.isExact h₂.isExact

/-- Beck-Chevalley condition for functor categories -/
def beckChevalleyFunctor {S : Square K L M N} [h : BeckChevalley S] (G : Type*) [Category G] :
    BeckChevalley (Square.mk (by simp [S.comm])) where
  isPullback := IsPullback.functor h.isPullback
  isFullyFaithful := ⟨Full.functor h.isFullyFaithful.1, Faithful.functor h.isFullyFaithful.2⟩
  isExact := Exact.functor h.isExact

end EndKan.Kan.BeckChevalley
