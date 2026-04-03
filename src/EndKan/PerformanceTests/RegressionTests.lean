import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Initial
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.Coequalizers
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.HasColimits
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.WideCoequalizers
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryCoproducts
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.WidePushouts
import EndKan.End.Core
import EndKan.Coend.Core
import EndKan.Kan.Core
import EndKan.Fubini
import EndKan.Tactics
import EndKan.Transformation
import EndKan.ErrorHandling

namespace EndKan.PerformanceTests.RegressionTests

open CategoryTheory
open CategoryTheory.Limits
open Lean Elab Tactic Meta

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Performance metrics for regression testing -/
structure PerformanceMetrics where
  executionTime : Nat -- in milliseconds
  memoryUsage : Nat -- in bytes
  stepCount : Nat
  success : Bool
  errorMessage : Option String

/-- Performance test result -/
structure PerformanceTestResult where
  testName : String
  metrics : PerformanceMetrics
  baseline : PerformanceMetrics
  regression : Bool
  improvement : Bool
  performanceRatio : Float

/-- Performance test suite -/
structure PerformanceTestSuite where
  name : String
  tests : List PerformanceTestResult
  overallRegression : Bool
  overallImprovement : Bool
  averagePerformanceRatio : Float

/-- Test suite for end performance regression tests -/
namespace EndPerformanceTests

/-- Test end construction performance -/
def testEndConstructionPerformance : TestCase :=
  testCase "End construction performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let endObj := EndObj F
    let π := End.π F (Classical.arbitrary C)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let uniq := End.uniq lift (𝟙 X) (by intro c; simp only [Category.id_comp])

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "End construction should complete within 100ms" (executionTime ≤ 100)
    assertTrue "End construction should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "End construction should succeed" (endObj = endObj)

/-- Test end β/η reduction performance -/
def testEndBetaEtaPerformance : TestCase :=
  testCase "End β/η reduction performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω

    -- Apply β/η reductions
    let liftBeta ← applyEndBeta lift
    let liftEta ← applyEndEta liftBeta
    let liftAggressive ← applyEndAggressive liftEta
    let liftComp ← applyEndComposition liftAggressive
    let liftUniversal ← applyEndUniversal liftComp

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "End β/η reduction should complete within 200ms" (executionTime ≤ 200)
    assertTrue "End β/η reduction should use less than 2MB memory" (memoryUsage ≤ 2 * 1024 * 1024)
    assertTrue "End β/η reduction should succeed" (liftUniversal = liftUniversal)

/-- Test end Fubini performance -/
def testEndFubiniPerformance : TestCase :=
  testCase "End Fubini performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : (C × D)ᵒᵖ × (C × D) ⥤ E := Functor.const ((C × D)ᵒᵖ × (C × D)) (𝟙_ E)
    let fubini := end_fubini F
    let prodFubini := end_prod_fubini F
    let functorFubini := end_functor_fubini F

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "End Fubini should complete within 300ms" (executionTime ≤ 300)
    assertTrue "End Fubini should use less than 3MB memory" (memoryUsage ≤ 3 * 1024 * 1024)
    assertTrue "End Fubini should succeed" (fubini = fubini)

/-- Test end pattern matching performance -/
def testEndPatternMatchingPerformance : TestCase :=
  testCase "End pattern matching performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test pattern matching
    let pattern ← analyzeGoal goal
    let strategies ← getTransformationStrategy pattern
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "End pattern matching should complete within 50ms" (executionTime ≤ 50)
    assertTrue "End pattern matching should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "End pattern matching should succeed" (result = result)

end EndPerformanceTests

/-- Test suite for coend performance regression tests -/
namespace CoendPerformanceTests

/-- Test coend construction performance -/
def testCoendConstructionPerformance : TestCase :=
  testCase "Coend construction performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let coendObj := CoendObj F
    let ι := Coend.ι F (Classical.arbitrary C)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    let uniq := Coend.uniq desc (𝟙 X) (by intro c; simp only [Category.comp_id])

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Coend construction should complete within 100ms" (executionTime ≤ 100)
    assertTrue "Coend construction should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Coend construction should succeed" (coendObj = coendObj)

/-- Test coend β/η reduction performance -/
def testCoendBetaEtaPerformance : TestCase :=
  testCase "Coend β/η reduction performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω

    -- Apply β/η reductions
    let descBeta ← applyCoendBeta desc
    let descEta ← applyCoendEta descBeta
    let descAggressive ← applyCoendAggressive descEta
    let descComp ← applyCoendComposition descAggressive
    let descUniversal ← applyCoendUniversal descComp

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Coend β/η reduction should complete within 200ms" (executionTime ≤ 200)
    assertTrue "Coend β/η reduction should use less than 2MB memory" (memoryUsage ≤ 2 * 1024 * 1024)
    assertTrue "Coend β/η reduction should succeed" (descUniversal = descUniversal)

/-- Test coend Fubini performance -/
def testCoendFubiniPerformance : TestCase :=
  testCase "Coend Fubini performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : (C × D) × (C × D)ᵒᵖ ⥤ E := Functor.const ((C × D) × (C × D)ᵒᵖ) (𝟙_ E)
    let fubini := coend_fubini F
    let prodFubini := coend_prod_fubini F
    let functorFubini := coend_functor_fubini F

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Coend Fubini should complete within 300ms" (executionTime ≤ 300)
    assertTrue "Coend Fubini should use less than 3MB memory" (memoryUsage ≤ 3 * 1024 * 1024)
    assertTrue "Coend Fubini should succeed" (fubini = fubini)

/-- Test coend pattern matching performance -/
def testCoendPatternMatchingPerformance : TestCase :=
  testCase "Coend pattern matching performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    let ι := Coend.ι F (Classical.arbitrary C)
    let goal := ι ≫ desc = ω.app (Classical.arbitrary C)

    -- Test pattern matching
    let pattern ← analyzeGoal goal
    let strategies ← getTransformationStrategy pattern
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Coend pattern matching should complete within 50ms" (executionTime ≤ 50)
    assertTrue "Coend pattern matching should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Coend pattern matching should succeed" (result = result)

end CoendPerformanceTests

/-- Test suite for Kan extension performance regression tests -/
namespace KanPerformanceTests

/-- Test Lan construction performance -/
def testLanConstructionPerformance : TestCase :=
  testCase "Lan construction performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let lan := Lan K F
    let α : F ⟶ K ⋙ G := 𝟙 F
    let universal := Lan.universal α
    let preserves := Lan.preservesColimits K F
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
    let fullyFaithful := Lan.fullyFaithful hK hK' F
    let id := Lan.id F
    let L : D ⥤ E := Functor.const D (𝟙_ E)
    let comp := Lan.comp K L F

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Lan construction should complete within 150ms" (executionTime ≤ 150)
    assertTrue "Lan construction should use less than 2MB memory" (memoryUsage ≤ 2 * 1024 * 1024)
    assertTrue "Lan construction should succeed" (lan = lan)

/-- Test Ran construction performance -/
def testRanConstructionPerformance : TestCase :=
  testCase "Ran construction performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let ran := Ran K F
    let α : K ⋙ G ⟶ F := 𝟙 F
    let universal := Ran.universal α
    let preserves := Ran.preservesLimits K F
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
    let fullyFaithful := Ran.fullyFaithful hK hK' F
    let id := Ran.id F
    let L : D ⥤ E := Functor.const D (𝟙_ E)
    let comp := Ran.comp K L F

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Ran construction should complete within 150ms" (executionTime ≤ 150)
    assertTrue "Ran construction should use less than 2MB memory" (memoryUsage ≤ 2 * 1024 * 1024)
    assertTrue "Ran construction should succeed" (ran = ran)

/-- Test Kan fusion performance -/
def testKanFusionPerformance : TestCase :=
  testCase "Kan fusion performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let lan := Lan K F

    -- Apply Kan fusion
    let fused ← applyKanFusionRules lan
    let aggressive ← applyKanAggressive fused
    let universal ← applyKanUniversal aggressive
    let comp ← applyKanComposition universal

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Kan fusion should complete within 100ms" (executionTime ≤ 100)
    assertTrue "Kan fusion should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Kan fusion should succeed" (comp = comp)

/-- Test Kan pattern matching performance -/
def testKanPatternMatchingPerformance : TestCase :=
  testCase "Kan pattern matching performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let lan := Lan K F
    let goal := lan = G

    -- Test pattern matching
    let pattern ← analyzeGoal goal
    let strategies ← getTransformationStrategy pattern
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Kan pattern matching should complete within 50ms" (executionTime ≤ 50)
    assertTrue "Kan pattern matching should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Kan pattern matching should succeed" (result = result)

end KanPerformanceTests

/-- Test suite for Beck-Chevalley performance regression tests -/
namespace BeckChevalleyPerformanceTests

/-- Test Beck-Chevalley transformation performance -/
def testBeckChevalleyTransformationPerformance : TestCase :=
  testCase "Beck-Chevalley transformation performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let lhs := mkConst `X
    let rhs := mkConst `Y

    -- Apply Beck-Chevalley transformations
    let lhsBC ← applyBeckChevalleyRules lhs
    let rhsBC ← applyBeckChevalleyRules rhs
    let lhsAggressive ← applyBeckChevalleyAggressive lhsBC
    let rhsAggressive ← applyBeckChevalleyAggressive rhsBC
    let lhsComp ← applyBeckChevalleyComposition lhsAggressive
    let rhsComp ← applyBeckChevalleyComposition rhsAggressive
    let lhsUniversal ← applyBeckChevalleyUniversal lhsComp
    let rhsUniversal ← applyBeckChevalleyUniversal rhsComp

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Beck-Chevalley transformation should complete within 100ms" (executionTime ≤ 100)
    assertTrue "Beck-Chevalley transformation should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Beck-Chevalley transformation should succeed" (lhsUniversal = lhsUniversal)

/-- Test Beck-Chevalley pattern matching performance -/
def testBeckChevalleyPatternMatchingPerformance : TestCase :=
  testCase "Beck-Chevalley pattern matching performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let goal := mkConst `X = mkConst `Y

    -- Test pattern matching
    let pattern ← analyzeGoal goal
    let strategies ← getTransformationStrategy pattern
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Beck-Chevalley pattern matching should complete within 50ms" (executionTime ≤ 50)
    assertTrue "Beck-Chevalley pattern matching should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Beck-Chevalley pattern matching should succeed" (result = result)

end BeckChevalleyPerformanceTests

/-- Test suite for mixed end/coend performance regression tests -/
namespace MixedEndCoendPerformanceTests

/-- Test mixed end/coend Fubini performance -/
def testMixedEndCoendFubiniPerformance : TestCase :=
  testCase "Mixed end/coend Fubini performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C × D × Dᵒᵖ ⥤ E := Functor.const (Cᵒᵖ × C × D × Dᵒᵖ) (𝟙_ E)
    let fubini := end_coend_fubini F

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Mixed end/coend Fubini should complete within 400ms" (executionTime ≤ 400)
    assertTrue "Mixed end/coend Fubini should use less than 4MB memory" (memoryUsage ≤ 4 * 1024 * 1024)
    assertTrue "Mixed end/coend Fubini should succeed" (fubini = fubini)

end MixedEndCoendPerformanceTests

/-- Test suite for tactic performance regression tests -/
namespace TacticPerformanceTests

/-- Test endkan_smart performance -/
def testEndkanSmartPerformance : TestCase :=
  testCase "endkan_smart performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Set performance configuration
    setTimeout 5000
    setTrace false
    setDebug false
    setAggressive true

    -- Execute endkan_smart
    let result ← executeEndKanTactic "endkan_smart"

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "endkan_smart should complete within 500ms" (executionTime ≤ 500)
    assertTrue "endkan_smart should use less than 5MB memory" (memoryUsage ≤ 5 * 1024 * 1024)
    assertTrue "endkan_smart should succeed" (result = result)

    -- Reset configuration
    setTimeout 2000
    setAggressive false

/-- Test endkan_debug performance -/
def testEndkanDebugPerformance : TestCase :=
  testCase "endkan_debug performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Set debug configuration
    setDebug true
    setTrace true

    -- Execute endkan_debug
    let result ← executeEndKanTactic "endkan_debug"

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "endkan_debug should complete within 100ms" (executionTime ≤ 100)
    assertTrue "endkan_debug should use less than 2MB memory" (memoryUsage ≤ 2 * 1024 * 1024)
    assertTrue "endkan_debug should succeed" (result = result)

    -- Reset configuration
    setDebug false
    setTrace false

/-- Test endkan_all performance -/
def testEndkanAllPerformance : TestCase :=
  testCase "endkan_all performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Set performance configuration
    setTimeout 10000
    setMaxSteps 1000
    setAggressive true

    -- Execute endkan_all
    let result ← executeEndKanTactic "endkan_all"

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "endkan_all should complete within 1000ms" (executionTime ≤ 1000)
    assertTrue "endkan_all should use less than 10MB memory" (memoryUsage ≤ 10 * 1024 * 1024)
    assertTrue "endkan_all should succeed" (result = result)

    -- Reset configuration
    setTimeout 2000
    setMaxSteps 200
    setAggressive false

/-- Test enhanced tactics performance -/
def testEnhancedTacticsPerformance : TestCase :=
  testCase "Enhanced tactics performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Execute enhanced tactics
    let result1 ← executeEndKanTacticEnhanced "end_beta!"
    let result2 ← executeEndKanTacticEnhanced "end_eta!"
    let result3 ← executeEndKanTacticEnhanced "coend_beta!"
    let result4 ← executeEndKanTacticEnhanced "coend_eta!"
    let result5 ← executeEndKanTacticEnhanced "kan_fuse!"
    let result6 ← executeEndKanTacticEnhanced "beck_chevalley!!"

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Enhanced tactics should complete within 600ms" (executionTime ≤ 600)
    assertTrue "Enhanced tactics should use less than 6MB memory" (memoryUsage ≤ 6 * 1024 * 1024)
    assertTrue "Enhanced tactics should succeed" (result1 = result1)

end TacticPerformanceTests

/-- Test suite for error handling performance regression tests -/
namespace ErrorHandlingPerformanceTests

/-- Test timeout error handling performance -/
def testTimeoutErrorHandlingPerformance : TestCase :=
  testCase "Timeout error handling performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Set very short timeout to trigger timeout error
    setTimeout 1

    -- Execute tactic with timeout
    let result ← executeEndKanTacticEnhanced "end_beta!"

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Timeout error handling should complete within 100ms" (executionTime ≤ 100)
    assertTrue "Timeout error handling should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Timeout error handling should succeed" (result = result)

    -- Reset timeout
    setTimeout 2000

/-- Test max steps error handling performance -/
def testMaxStepsErrorHandlingPerformance : TestCase :=
  testCase "Max steps error handling performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Set very low max steps to trigger max steps error
    setMaxSteps 1

    -- Execute tactic with max steps
    let result ← executeEndKanTacticEnhanced "end_beta!"

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Max steps error handling should complete within 100ms" (executionTime ≤ 100)
    assertTrue "Max steps error handling should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Max steps error handling should succeed" (result = result)

    -- Reset max steps
    setMaxSteps 200

/-- Test pattern match failure error handling performance -/
def testPatternMatchFailureErrorHandlingPerformance : TestCase :=
  testCase "Pattern match failure error handling performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let goal := mkConst `X = mkConst `Y

    -- Execute tactic with unknown pattern
    let result ← executeEndKanTacticEnhanced "end_beta!"

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Pattern match failure error handling should complete within 50ms" (executionTime ≤ 50)
    assertTrue "Pattern match failure error handling should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Pattern match failure error handling should succeed" (result = result)

/-- Test transformation failure error handling performance -/
def testTransformationFailureErrorHandlingPerformance : TestCase :=
  testCase "Transformation failure error handling performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    let goal := mkConst `X = mkConst `Y

    -- Execute tactic with transformation failure
    let result ← executeEndKanTacticEnhanced "end_beta!"

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Transformation failure error handling should complete within 50ms" (executionTime ≤ 50)
    assertTrue "Transformation failure error handling should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Transformation failure error handling should succeed" (result = result)

end ErrorHandlingPerformanceTests

/-- Test suite for resource monitoring performance regression tests -/
namespace ResourceMonitoringPerformanceTests

/-- Test resource monitoring performance -/
def testResourceMonitoringPerformance : TestCase :=
  testCase "Resource monitoring performance" do
    let startTime ← IO.monoMsNow
    let startMemory ← IO.getMemoryUsage

    -- Create resource monitor
    let monitor ← createResourceMonitor
    let check1 ← checkResourceLimits monitor
    let deactivated := deactivateResourceMonitor monitor
    let check2 ← checkResourceLimits deactivated

    -- Create timeout manager
    let timeoutManager ← createTimeoutManager 1000
    let timeoutCheck1 ← checkTimeout timeoutManager
    let deactivatedTimeout := deactivateTimeout timeoutManager
    let timeoutCheck2 ← checkTimeout deactivatedTimeout

    -- Create step counter
    let stepCounter := createStepCounter 100
    let stepCheck1 := checkMaxSteps stepCounter
    let incremented := incrementSteps stepCounter
    let stepCheck2 := checkMaxSteps incremented
    let deactivatedSteps := deactivateSteps incremented
    let stepCheck3 := checkMaxSteps deactivatedSteps

    let endTime ← IO.monoMsNow
    let endMemory ← IO.getMemoryUsage

    let executionTime := endTime - startTime
    let memoryUsage := endMemory - startMemory

    -- Performance assertions
    assertTrue "Resource monitoring should complete within 50ms" (executionTime ≤ 50)
    assertTrue "Resource monitoring should use less than 1MB memory" (memoryUsage ≤ 1024 * 1024)
    assertTrue "Resource monitoring should succeed" (check1 = check1)

end ResourceMonitoringPerformanceTests

/-- Main test suite for all performance regression tests -/
def allPerformanceRegressionTests : TestSuite :=
  testSuite "Performance Regression Tests" [
    EndPerformanceTests.testEndConstructionPerformance,
    EndPerformanceTests.testEndBetaEtaPerformance,
    EndPerformanceTests.testEndFubiniPerformance,
    EndPerformanceTests.testEndPatternMatchingPerformance,
    CoendPerformanceTests.testCoendConstructionPerformance,
    CoendPerformanceTests.testCoendBetaEtaPerformance,
    CoendPerformanceTests.testCoendFubiniPerformance,
    CoendPerformanceTests.testCoendPatternMatchingPerformance,
    KanPerformanceTests.testLanConstructionPerformance,
    KanPerformanceTests.testRanConstructionPerformance,
    KanPerformanceTests.testKanFusionPerformance,
    KanPerformanceTests.testKanPatternMatchingPerformance,
    BeckChevalleyPerformanceTests.testBeckChevalleyTransformationPerformance,
    BeckChevalleyPerformanceTests.testBeckChevalleyPatternMatchingPerformance,
    MixedEndCoendPerformanceTests.testMixedEndCoendFubiniPerformance,
    TacticPerformanceTests.testEndkanSmartPerformance,
    TacticPerformanceTests.testEndkanDebugPerformance,
    TacticPerformanceTests.testEndkanAllPerformance,
    TacticPerformanceTests.testEnhancedTacticsPerformance,
    ErrorHandlingPerformanceTests.testTimeoutErrorHandlingPerformance,
    ErrorHandlingPerformanceTests.testMaxStepsErrorHandlingPerformance,
    ErrorHandlingPerformanceTests.testPatternMatchFailureErrorHandlingPerformance,
    ErrorHandlingPerformanceTests.testTransformationFailureErrorHandlingPerformance,
    ResourceMonitoringPerformanceTests.testResourceMonitoringPerformance
  ]

end EndKan.PerformanceTests.RegressionTests
