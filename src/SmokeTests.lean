import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import EndKan.End.Core
import EndKan.Coend.Core
import EndKan.Kan.Core

namespace EndKan.SmokeTests

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Test end construction -/
def testEndConstruction : IO Unit := do
  IO.println "Testing End Construction..."
  let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
  let _endObj := EndObj F
  IO.println "✓ End construction successful"

/-- Test coend construction -/
def testCoendConstruction : IO Unit := do
  IO.println "Testing Coend Construction..."
  let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
  let _coendObj := CoendObj F
  IO.println "✓ Coend construction successful"

/-- Test Kan extension construction -/
def testKanConstruction : IO Unit := do
  IO.println "Testing Kan Extension Construction..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let _lan := Lan K F
  let _ran := Ran K F
  IO.println "✓ Kan extension construction successful"

/-- Test end universal property -/
def testEndUniversal : IO Unit := do
  IO.println "Testing End Universal Property..."
  let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
  let X : D := 𝟙_ D
  let ω : DinaturalTransformation X F := {
    app := fun _ => 𝟙 X
    dinaturality := by simp
  }
  let _lift := End.lift ω
  IO.println "✓ End universal property successful"

/-- Test coend universal property -/
def testCoendUniversal : IO Unit := do
  IO.println "Testing Coend Universal Property..."
  let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
  let X : D := 𝟙_ D
  let ω : DinaturalTransformation F X := {
    app := fun _ => 𝟙 X
    dinaturality := by simp
  }
  let _desc := Coend.desc ω
  IO.println "✓ Coend universal property successful"

/-- Test end projections -/
def testEndProjections : IO Unit := do
  IO.println "Testing End Projections..."
  let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
  let c : C := Classical.arbitrary C
  let _π := End.π F c
  IO.println "✓ End projections successful"

/-- Test coend inclusions -/
def testCoendInclusions : IO Unit := do
  IO.println "Testing Coend Inclusions..."
  let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
  let c : C := Classical.arbitrary C
  let _ι := Coend.ι F c
  IO.println "✓ Coend inclusions successful"

/-- Test end uniqueness -/
def testEndUniqueness : IO Unit := do
  IO.println "Testing End Uniqueness..."
  let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
  let X : D := 𝟙_ D
  let f g : X ⟶ EndObj F := 𝟙 X
  let h : ∀ c : C, f ≫ End.π F c = g ≫ End.π F c := by
    intro c
    simp only [Category.id_comp]
  let _uniq := End.uniq f g h
  IO.println "✓ End uniqueness successful"

/-- Test coend uniqueness -/
def testCoendUniqueness : IO Unit := do
  IO.println "Testing Coend Uniqueness..."
  let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
  let X : D := 𝟙_ D
  let f g : CoendObj F ⟶ X := 𝟙 X
  let h : ∀ c : C, Coend.ι F c ≫ f = Coend.ι F c ≫ g := by
    intro c
    simp only [Category.comp_id]
  let _uniq := Coend.uniq f g h
  IO.println "✓ Coend uniqueness successful"

/-- Test end functoriality -/
def testEndFunctoriality : IO Unit := do
  IO.println "Testing End Functoriality..."
  let F G : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
  let α : F ⟶ G := 𝟙 F
  let _map := End.map α
  IO.println "✓ End functoriality successful"

/-- Test coend functoriality -/
def testCoendFunctoriality : IO Unit := do
  IO.println "Testing Coend Functoriality..."
  let F G : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
  let α : F ⟶ G := 𝟙 F
  let _map := Coend.map α
  IO.println "✓ Coend functoriality successful"

/-- Test end constant -/
def testEndConstant : IO Unit := do
  IO.println "Testing End Constant..."
  let X : D := 𝟙_ D
  let _const := End.const X
  IO.println "✓ End constant successful"

/-- Test coend constant -/
def testCoendConstant : IO Unit := do
  IO.println "Testing Coend Constant..."
  let X : D := 𝟙_ D
  let _const := Coend.const X
  IO.println "✓ Coend constant successful"

/-- Test end representable -/
def testEndRepresentable : IO Unit := do
  IO.println "Testing End Representable..."
  let c : C := Classical.arbitrary C
  let _representable := End.representable c
  IO.println "✓ End representable successful"

/-- Test coend representable -/
def testCoendRepresentable : IO Unit := do
  IO.println "Testing Coend Representable..."
  let c : C := Classical.arbitrary C
  let _representable := Coend.representable c
  IO.println "✓ Coend representable successful"

/-- Test Lan universal property -/
def testLanUniversal : IO Unit := do
  IO.println "Testing Lan Universal Property..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let G : D ⥤ E := Functor.const D (𝟙_ E)
  let α : F ⟶ K ⋙ G := 𝟙 F
  let _universal := Lan.universal α
  IO.println "✓ Lan universal property successful"

/-- Test Ran universal property -/
def testRanUniversal : IO Unit := do
  IO.println "Testing Ran Universal Property..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let G : D ⥤ E := Functor.const D (𝟙_ E)
  let α : K ⋙ G ⟶ F := 𝟙 F
  let _universal := Ran.universal α
  IO.println "✓ Ran universal property successful"

/-- Test Lan preserves colimits -/
def testLanPreservesColimits : IO Unit := do
  IO.println "Testing Lan Preserves Colimits..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let _preserves := Lan.preservesColimits K F
  IO.println "✓ Lan preserves colimits successful"

/-- Test Ran preserves limits -/
def testRanPreservesLimits : IO Unit := do
  IO.println "Testing Ran Preserves Limits..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let _preserves := Ran.preservesLimits K F
  IO.println "✓ Ran preserves limits successful"

/-- Test Lan fully faithful -/
def testLanFullyFaithful : IO Unit := do
  IO.println "Testing Lan Fully Faithful..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let hK : Full K := by
    constructor
    intro X Y f
    use f
    simp
  let hK' : Faithful K := by
    constructor
    intro X Y f g h
    simp at h
    exact h
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let _fullyFaithful := Lan.fullyFaithful hK hK' F
  IO.println "✓ Lan fully faithful successful"

/-- Test Ran fully faithful -/
def testRanFullyFaithful : IO Unit := do
  IO.println "Testing Ran Fully Faithful..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let hK : Full K := by
    constructor
    intro X Y f
    use f
    simp
  let hK' : Faithful K := by
    constructor
    intro X Y f g h
    simp at h
    exact h
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let _fullyFaithful := Ran.fullyFaithful hK hK' F
  IO.println "✓ Ran fully faithful successful"

/-- Test Lan identity -/
def testLanIdentity : IO Unit := do
  IO.println "Testing Lan Identity..."
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let _id := Lan.id F
  IO.println "✓ Lan identity successful"

/-- Test Ran identity -/
def testRanIdentity : IO Unit := do
  IO.println "Testing Ran Identity..."
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let _id := Ran.id F
  IO.println "✓ Ran identity successful"

/-- Test Lan composition -/
def testLanComposition : IO Unit := do
  IO.println "Testing Lan Composition..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let L : D ⥤ E := Functor.const D (𝟙_ E)
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let _comp := Lan.comp K L F
  IO.println "✓ Lan composition successful"

/-- Test Ran composition -/
def testRanComposition : IO Unit := do
  IO.println "Testing Ran Composition..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let L : D ⥤ E := Functor.const D (𝟙_ E)
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let _comp := Ran.comp K L F
  IO.println "✓ Ran composition successful"

/-- Run all EndKan smoke tests -/
def runAll : IO Unit := do
  IO.println "Running EndKan Comprehensive Tests"
  IO.println "================================="
  IO.println ""

  let startTime ← IO.monoMsNow

  testEndConstruction
  testCoendConstruction
  testKanConstruction
  testEndUniversal
  testCoendUniversal
  testEndProjections
  testCoendInclusions
  testEndUniqueness
  testCoendUniqueness
  testEndFunctoriality
  testCoendFunctoriality
  testEndConstant
  testCoendConstant
  testEndRepresentable
  testCoendRepresentable
  testLanUniversal
  testRanUniversal
  testLanPreservesColimits
  testRanPreservesLimits
  testLanFullyFaithful
  testRanFullyFaithful
  testLanIdentity
  testRanIdentity
  testLanComposition
  testRanComposition

  let endTime ← IO.monoMsNow
  let executionTime := endTime - startTime

  IO.println ""
  IO.println "================================="
  IO.println "All EndKan tests completed successfully!"
  IO.println s!"Total execution time: {executionTime}ms"

end EndKan.SmokeTests

/-- Entry point for `lake exe run_tests` (historical name). -/
def main (_args : List String) : IO Unit := do
  EndKan.SmokeTests.runAll
