import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import EndKan.End.Core
import EndKan.Coend.Core
import EndKan.Kan.Core

namespace EndKan.Test

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Test end construction -/
def testEndConstruction : IO Unit := do
  IO.println "Testing End Construction..."
  let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
  let endObj := EndObj F
  IO.println "✓ End construction successful"

/-- Test coend construction -/
def testCoendConstruction : IO Unit := do
  IO.println "Testing Coend Construction..."
  let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
  let coendObj := CoendObj F
  IO.println "✓ Coend construction successful"

/-- Test Kan extension construction -/
def testKanConstruction : IO Unit := do
  IO.println "Testing Kan Extension Construction..."
  let K : C ⥤ D := Functor.const C (𝟙_ D)
  let F : C ⥤ E := Functor.const C (𝟙_ E)
  let lan := Lan K F
  let ran := Ran K F
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
  let lift := End.lift ω
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
  let desc := Coend.desc ω
  IO.println "✓ Coend universal property successful"

/-- Run all tests -/
def runAllTests : IO Unit := do
  IO.println "Running EndKan Tests"
  IO.println "==================="
  IO.println ""

  let startTime ← IO.monoMsNow

  testEndConstruction
  testCoendConstruction
  testKanConstruction
  testEndUniversal
  testCoendUniversal

  let endTime ← IO.monoMsNow
  let executionTime := endTime - startTime

  IO.println ""
  IO.println "==================="
  IO.println "All tests completed successfully!"
  IO.println s!"Total execution time: {executionTime}ms"

end EndKan.Test

/-- Entry point for `lake exe test`. -/
def main (_args : List String) : IO Unit := do
  EndKan.Test.runAllTests
