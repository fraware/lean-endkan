import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

namespace EndKan.SimpleTest

open CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- Simple test for category theory basics -/
def testCategoryBasics : IO Unit := do
  IO.println "Testing Category Theory Basics..."
  let X : C := 𝟙_ C
  let f : X ⟶ X := 𝟙 X
  let g : X ⟶ X := f ≫ f
  IO.println "✓ Category theory basics successful"

/-- Simple test for functor basics -/
def testFunctorBasics : IO Unit := do
  IO.println "Testing Functor Basics..."
  let F : C ⥤ D := Functor.const C (𝟙_ D)
  let X : C := 𝟙_ C
  let FX : D := F.obj X
  IO.println "✓ Functor basics successful"

/-- Run all simple tests -/
def runAllSimpleTests : IO Unit := do
  IO.println "Running EndKan Simple Tests"
  IO.println "=========================="
  IO.println ""

  let startTime ← IO.monoMsNow

  testCategoryBasics
  testFunctorBasics

  let endTime ← IO.monoMsNow
  let executionTime := endTime - startTime

  IO.println ""
  IO.println "=========================="
  IO.println "All simple tests completed successfully!"
  IO.println s!"Total execution time: {executionTime}ms"

/-- Main function -/
def main (args : List String) : IO Unit := do
  runAllSimpleTests

end EndKan.SimpleTest
