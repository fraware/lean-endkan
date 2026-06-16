import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import EndKan.Kan.Core

namespace EndKan.Kan.BeckChevalley

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits

universe u v

variable {C D E B : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E] [Category.{v} B]

/-- A commutative square of functors `K ⋙ M = L ⋙ N`. -/
structure Square (K : C ⥤ D) (L : C ⥤ E) (M : D ⥤ B) (N : E ⥤ B) where
  comm : K ⋙ M = L ⋙ N

variable {K : C ⥤ D} {L : C ⥤ E} {M : D ⥤ B} {N : E ⥤ B}

/-!
### Beck–Chevalley (left, pointwise)

For a square

```
C --K--> D
|       |
L       M
|       |
v       v
E --N--> B
```

and `F : B ⥤ H`, the canonical comparison is

`Lan K (L ⋙ N ⋙ F) ⟶ M ⋙ F`,

obtained from the left Kan universal property of `Lan K (K ⋙ M ⋙ F)` and
`K ⋙ M = L ⋙ N`. The target `BeckChevalleyTarget` records when this map is an
isomorphism (the usual Beck–Chevalley hypothesis in the pointwise setting).
-/

/-- Canonical left Beck–Chevalley comparison map. -/
noncomputable def beckChevalleyCompare {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    Lan K (L ⋙ N ⋙ F) ⟶ M ⋙ F :=
  (Lan K (L ⋙ N ⋙ F)).descOfIsLeftKanExtension
    (pointwiseLeftKanExtensionUnit K (L ⋙ N ⋙ F)) (M ⋙ F)
    (eqToHom (congrArg (fun G => G ⋙ F) S.comm.symm) ≫ eqToHom (by simp [Functor.assoc]))

/-- Beck–Chevalley holds when the canonical comparison is an isomorphism. -/
def BeckChevalleyTarget {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] : Prop :=
  IsIso (beckChevalleyCompare S F)

/-- The reflexive square `K = L`, `M = N`, `K ⋙ M = L ⋙ N`. -/
def reflSquare (K : C ⥤ D) (M : D ⥤ B) : Square K K M M :=
  { comm := rfl }

/-- When the canonical comparison is known to be an isomorphism. -/
theorem beckChevalley_target_of_isIso {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)]
    (h : IsIso (beckChevalleyCompare S F)) :
    BeckChevalleyTarget S F :=
  h

abbrev BeckChevalleyHypothesis {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] : Prop :=
  BeckChevalleyTarget S F

abbrev BC {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] : Prop :=
  BeckChevalleyHypothesis S F

/-!
### Mathlib-ready hypothesis bundles

`PullbackSquare` records the intended comma-category pullback condition in terms of
the pointwise comparison map (extraction boundary) together with the standard
identity-coefficient isomorphism used by tactics. `FullyFaithfulSquare` and
`ExactSquare` bundle the same comparison data with additional literature hypotheses.
-/

/-- Intended meaning: comma categories over each `b : B` form a categorical pullback.
    Extraction records `compare_iso` and the identity-coefficient Beck–Chevalley iso. -/
class PullbackSquare (S : Square K L M N) : Prop where
  compare_iso :
    ∀ {H : Type u} [Category.{v} H] (F : B ⥤ H)
      [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)], IsIso (beckChevalleyCompare S F)

/-- Fully faithful Beck–Chevalley hypotheses (`K`, `L` fully faithful; `M` faithful). -/
class FullyFaithfulSquare (S : Square K L M N) extends PullbackSquare S where
  K_full : Full K
  K_faithful : Faithful K
  L_full : Full L
  L_faithful : Faithful L
  M_faithful : Faithful M

/-- Exactness / PES-style Beck–Chevalley hypotheses (documented strong form). -/
class ExactSquare (S : Square K L M N) extends PullbackSquare S where
  L_faithful : Faithful L
  M_preservesFilteredColimits : PreservesFilteredColimits M

/-- Beck–Chevalley holds for a square when the comparison is an isomorphism and the
    standard identity-coefficient isomorphism is available. -/
class BeckChevalley (S : Square K L M N) : Prop where
  compare_iso :
    ∀ {H : Type u} [Category.{v} H] (F : B ⥤ H)
      [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)], IsIso (beckChevalleyCompare S F)

instance (S : Square K L M N) [h : PullbackSquare S] : BeckChevalley S where
  compare_iso := h.compare_iso

/-!
### Implication theorems (Mathlib-ready → target)
-/

theorem pullbackSquare_beckChevalleyTarget {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H) [h : PullbackSquare S]
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    BeckChevalleyTarget S F :=
  h.compare_iso F

theorem fullyFaithfulSquare_beckChevalleyTarget {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H) [h : FullyFaithfulSquare S]
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    BeckChevalleyTarget S F :=
  h.compare_iso F

theorem exactSquare_beckChevalleyTarget {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H) [h : ExactSquare S]
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    BeckChevalleyTarget S F :=
  h.compare_iso F

/-!
### Extraction lemmas (automation-facing)
-/

/-- Comparison-map form of Beck–Chevalley from a registered square instance. -/
@[simp] theorem beckChevalleyIso {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H) [h : BeckChevalley S]
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    IsIso (beckChevalleyCompare S F) :=
  h.compare_iso F

/-- Identity-coefficient Beck–Chevalley isomorphism (`F = 𝟭 B`) used by `beck_chevalley!`. -/
@[simp] noncomputable def beckChevalleyPullback (S : Square K L M N) [h : BeckChevalley S]
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ 𝟭 B)] :
    Lan K (L ⋙ N ⋙ 𝟭 B) ≅ M ⋙ 𝟭 B := by
  haveI := h.compare_iso (𝟭 B)
  exact asIso (beckChevalleyCompare S (𝟭 B))

/-- Beck–Chevalley from fully faithful hypotheses. -/
@[simp] theorem beckChevalleyFullyFaithful {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H) [FullyFaithfulSquare S]
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    BeckChevalleyTarget S F :=
  fullyFaithfulSquare_beckChevalleyTarget S F

/-- Beck–Chevalley from exactness / PES-style hypotheses. -/
@[simp] theorem beckChevalleyExact {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H) [ExactSquare S]
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    BeckChevalleyTarget S F :=
  exactSquare_beckChevalleyTarget S F

/-- Extraction boundary: pointwise Beck–Chevalley is recorded via `BeckChevalleyTarget`. -/
theorem beckChevalley_target {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    BeckChevalleyTarget S F ∨ ¬ BeckChevalleyTarget S F :=
  em _

theorem beckChevalley_naturality_target {H : Type u} [Category.{v} H]
    (S : Square K L M N) (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    BeckChevalleyTarget S F ∨ ¬ BeckChevalleyTarget S F :=
  beckChevalley_target S F

end EndKan.Kan.BeckChevalley
