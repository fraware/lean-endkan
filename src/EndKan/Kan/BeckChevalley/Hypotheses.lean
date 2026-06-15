import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import EndKan.Kan.Core
import EndKan.Kan.BeckChevalley

namespace EndKan.Kan.BeckChevalley

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open EndKan.Kan

universe u v

variable {C D E B : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E] [Category.{v} B]
variable {K : C ⥤ D} {L : C ⥤ E} {M : D ⥤ B} {N : E ⥤ B}
variable {H : Type u} [Category.{v} H]

/-!
### Geometric Beck–Chevalley hypotheses (Phase 4B)

`IsPullbackSquare` records the intended comma-category pullback formulation.
A full Beck–Chevalley proof from finality of comma projections is not yet
available in Mathlib; `pullbackSquare_of_equivalence` derives the comparison
isomorphism from `[IsEquivalence K]`.
-/

/-- Intended geometric meaning: comma categories over each `b : B` form a pullback.
    The comparison isomorphism is the extraction boundary; see
    `pullbackSquare_of_equivalence` for a Mathlib-derived proof.

    Comma-side types at base object `b` are `beckChevalleySouth` / `beckChevalleyNorth`
    (`StructuredArrow b M` and `StructuredArrow b N`). A full proof would relate the
    comma projections `(K ↓ M⁻¹b)` and `(L ↓ N⁻¹b)` to these legs and invoke finality
    (`Comma.final_fst`); that step remains upstream. -/
class IsPullbackSquare (S : Square K L M N) extends PullbackSquare S where
  comma_pullback : Prop := True

instance (S : Square K L M N) [h : IsPullbackSquare S] : PullbackSquare S :=
  { compare_iso := h.compare_iso }

/-!
### Comparison helpers
-/

theorem square_whisker_eq (S : Square K L M N) (F : B ⥤ H) :
    L ⋙ N ⋙ F = K ⋙ M ⋙ F := by
  calc
    L ⋙ N ⋙ F = (L ⋙ N) ⋙ F := by simp [Functor.assoc]
    _ = (K ⋙ M) ⋙ F := by rw [S.comm]
    _ = K ⋙ M ⋙ F := by simp [Functor.assoc]

/-!
### Comma-category Beck–Chevalley staging (§10 research)

Mathlib supplies `StructuredArrow` (comma categories) and comma-projection finality
(`Mathlib.CategoryTheory.Comma.Final`, `Comma.final_fst`). The intended geometric pullback at
`b : B` compares comma categories built from the horizontal legs `M` and `N`;
`square_comm_whisker` is the functor-level input from `S.comm`. Deriving `compare_iso` from
comma finality alone is still a boundary.
-/

/-- Structured arrows over base object `b` along the south horizontal leg `M`. -/
abbrev beckChevalleySouth (b : B) := StructuredArrow b M

/-- Structured arrows over base object `b` along the north horizontal leg `N`. -/
abbrev beckChevalleyNorth (b : B) := StructuredArrow b N

/-- Commutativity of the square, after whiskering along `F` (comma-leg compatibility input). -/
theorem square_comm_whisker (S : Square K L M N) (F : B ⥤ H) :
    L ⋙ N ⋙ F = K ⋙ M ⋙ F :=
  square_whisker_eq S F

/-- On a reflexive square (`M = N`), south and north comma types at `b` agree definitionally. -/
theorem refl_beckChevalleySouth_eq (M : D ⥤ B) (b : B) :
    beckChevalleySouth (M := M) b = beckChevalleyNorth (N := M) b :=
  rfl

/-!
### Further comparison helpers
-/

/-- Unit natural transformation induced by a commutative square. -/
def squareExtensionUnit (S : Square K L M N) (F : B ⥤ H) :
    (L ⋙ N ⋙ F) ⟶ K ⋙ (M ⋙ F) :=
  eqToHom (congrArg (fun G => G ⋙ F) S.comm.symm) ≫ eqToHom (by simp [Functor.assoc])

@[simp]
theorem beckChevalleyCompare_refl (M : D ⥤ B) (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (K ⋙ M ⋙ F)] :
    beckChevalleyCompare (reflSquare K M) F =
      (Lan K (K ⋙ M ⋙ F)).descOfIsLeftKanExtension
        (pointwiseLeftKanExtensionUnit K (K ⋙ M ⋙ F)) (M ⋙ F) (𝟙 (K ⋙ M ⋙ F)) := by
  unfold beckChevalleyCompare reflSquare
  congr 1 <;> simp [eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

instance squareExtensionUnit_isIso (S : Square K L M N) (F : B ⥤ H) :
    IsIso (squareExtensionUnit S F) := by
  dsimp [squareExtensionUnit]
  infer_instance

theorem isLeftKanExtension_id_of_equivalence (G : D ⥤ H) [IsEquivalence K]
    [HasPointwiseLeftKanExtension K (K ⋙ G)] :
    (G).IsLeftKanExtension (𝟙 (K ⋙ G)) := by
  exact isLeftKanExtensionAlongEquivalence' K (𝟙 (K ⋙ G))

theorem isLeftKanExtension_square_of_equivalence (S : Square K L M N) (F : B ⥤ H)
    [IsEquivalence K] [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    (M ⋙ F).IsLeftKanExtension (squareExtensionUnit S F) := by
  exact isLeftKanExtensionAlongEquivalence' K (squareExtensionUnit S F)

/-- Left Kan extending a whiskered functor along an equivalence recovers the target. -/
noncomputable def Lan.whiskerCompIsoOfEquivalence (G : D ⥤ H) [IsEquivalence K]
    [HasPointwiseLeftKanExtension K (K ⋙ G)] :
    Lan K (K ⋙ G) ≅ G :=
  leftKanExtensionUnique _ (pointwiseLeftKanExtensionUnit K (K ⋙ G)) _ (𝟙 (K ⋙ G))

theorem isIso_beckChevalleyCompare_of_equivalence (S : Square K L M N) (F : B ⥤ H)
    [IsEquivalence K] [HasPointwiseLeftKanExtension K (L ⋙ N ⋙ F)] :
    IsIso (beckChevalleyCompare S F) := by
  have hle := isLeftKanExtension_square_of_equivalence S F
  exact (isLeftKanExtension_iff_isIso _ (pointwiseLeftKanExtensionUnit K (L ⋙ N ⋙ F)) _
    (by simp [beckChevalleyCompare, squareExtensionUnit])).mp hle

theorem isIso_beckChevalleyCompare_of_isLeftKanExtension_id (M : D ⥤ B) (F : B ⥤ H)
    [HasPointwiseLeftKanExtension K (K ⋙ M ⋙ F)]
    [h : (M ⋙ F).IsLeftKanExtension (𝟙 (K ⋙ M ⋙ F))] :
    IsIso (beckChevalleyCompare (reflSquare K M) F) := by
  rw [beckChevalleyCompare_refl]
  exact (isLeftKanExtension_iff_isIso _ (pointwiseLeftKanExtensionUnit K (K ⋙ M ⋙ F)) _
    (by simp)).mp h

/-!
### Fully faithful hypotheses
-/
theorem fullyFaithfulSquare_of_equivalence (S : Square K L M N) [IsEquivalence K]
    [IsEquivalence L] [Faithful M] [Full K] [Faithful K] [Full L] [Faithful L] :
    FullyFaithfulSquare S where
  compare_iso := fun F _ => isIso_beckChevalleyCompare_of_equivalence S F
  K_full := inferInstance
  K_faithful := inferInstance
  L_full := inferInstance
  L_faithful := inferInstance
  M_faithful := inferInstance

/-- Pullback Beck–Chevalley derived from equivalence on the vertical leg. -/
theorem pullbackSquare_of_equivalence (S : Square K L M N) [IsEquivalence K] :
    PullbackSquare S where
  compare_iso := fun F _ => isIso_beckChevalleyCompare_of_equivalence S F

/-!
### Reflexive and exact instances
-/

instance reflSquare_beckChevalley (M : D ⥤ B) [IsEquivalence K] : BeckChevalley (reflSquare K M) where
  compare_iso := fun F _ => isIso_beckChevalleyCompare_of_equivalence (reflSquare K M) F

instance (S : Square K L M N) [IsEquivalence K] : PullbackSquare S :=
  pullbackSquare_of_equivalence S

instance (S : Square K L M N) [IsEquivalence K] [IsEquivalence L] [Faithful M]
    [Full K] [Faithful K] [Full L] [Faithful L] : FullyFaithfulSquare S :=
  fullyFaithfulSquare_of_equivalence S

/-- Exactness / PES-style hypotheses (documented strong form). -/
theorem exactSquare_of_equivalence (S : Square K L M N) [IsEquivalence K]
    [Faithful L] [PreservesFilteredColimits M] :
    ExactSquare S where
  compare_iso := fun F _ => isIso_beckChevalleyCompare_of_equivalence S F
  L_faithful := inferInstance
  M_preservesFilteredColimits := inferInstance

/-!
### Compile-time fixtures (Kan regression)
-/

section compileFixture

variable (K : C ⥤ D) (M : D ⥤ B) [IsEquivalence K]

#check (inferInstance : BeckChevalley (reflSquare K M))
#check @beckChevalleySouth

end compileFixture

end EndKan.Kan.BeckChevalley
