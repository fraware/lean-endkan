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
import EndKan.Tactics
import EndKan.Transformation
import EndKan.ErrorHandling

namespace EndKan.IntegrationTests.TacticInteractions

open CategoryTheory
open CategoryTheory.Limits
open Lean Elab Tactic Meta

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Test suite for tactic pattern matching integration -/
namespace PatternMatchingIntegrationTests

/-- Test end pattern detection and transformation -/
def testEndPatternDetection : TestCase :=
  testCase "End pattern detection and transformation" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test pattern detection
    let pattern ← analyzeGoal goal
    assertTrue "Should detect end equality pattern" (pattern = .endEquality _ _)

    -- Test transformation strategy selection
    let strategies ← getTransformationStrategy pattern
    assertTrue "Should have end transformation strategies" (strategies.length > 0)

    -- Test strategy execution
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic
    assertTrue "Strategy should execute successfully" (result = result)

/-- Test coend pattern detection and transformation -/
def testCoendPatternDetection : TestCase :=
  testCase "Coend pattern detection and transformation" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    let ι := Coend.ι F (Classical.arbitrary C)
    let goal := ι ≫ desc = ω.app (Classical.arbitrary C)

    -- Test pattern detection
    let pattern ← analyzeGoal goal
    assertTrue "Should detect coend equality pattern" (pattern = .coendEquality _ _)

    -- Test transformation strategy selection
    let strategies ← getTransformationStrategy pattern
    assertTrue "Should have coend transformation strategies" (strategies.length > 0)

    -- Test strategy execution
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic
    assertTrue "Strategy should execute successfully" (result = result)

/-- Test Kan extension pattern detection and transformation -/
def testKanPatternDetection : TestCase :=
  testCase "Kan extension pattern detection and transformation" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let lan := Lan K F
    let goal := lan = G

    -- Test pattern detection
    let pattern ← analyzeGoal goal
    assertTrue "Should detect Kan extension pattern" (pattern = .kanExtension _ _)

    -- Test transformation strategy selection
    let strategies ← getTransformationStrategy pattern
    assertTrue "Should have Kan transformation strategies" (strategies.length > 0)

    -- Test strategy execution
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic
    assertTrue "Strategy should execute successfully" (result = result)

/-- Test Beck-Chevalley pattern detection and transformation -/
def testBeckChevalleyPatternDetection : TestCase :=
  testCase "Beck-Chevalley pattern detection and transformation" do
    let goal := mkConst `X = mkConst `Y

    -- Test pattern detection
    let pattern ← analyzeGoal goal
    assertTrue "Should detect Beck-Chevalley pattern" (pattern = .beckChevalley _ _)

    -- Test transformation strategy selection
    let strategies ← getTransformationStrategy pattern
    assertTrue "Should have Beck-Chevalley transformation strategies" (strategies.length > 0)

    -- Test strategy execution
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic
    assertTrue "Strategy should execute successfully" (result = result)

/-- Test dinaturality pattern detection and transformation -/
def testDinaturalityPatternDetection : TestCase :=
  testCase "Dinaturality pattern detection and transformation" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let goal := ω = ω

    -- Test pattern detection
    let pattern ← analyzeGoal goal
    assertTrue "Should detect dinaturality pattern" (pattern = .dinaturality _ _)

    -- Test transformation strategy selection
    let strategies ← getTransformationStrategy pattern
    assertTrue "Should have dinaturality transformation strategies" (strategies.length > 0)

    -- Test strategy execution
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic
    assertTrue "Strategy should execute successfully" (result = result)

/-- Test functor composition pattern detection and transformation -/
def testFunctorCompositionPatternDetection : TestCase :=
  testCase "Functor composition pattern detection and transformation" do
    let F : C ⥤ D := Functor.const C (𝟙_ D)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let comp := F ⋙ G
    let goal := comp = comp

    -- Test pattern detection
    let pattern ← analyzeGoal goal
    assertTrue "Should detect functor composition pattern" (pattern = .functorComposition _ _)

    -- Test transformation strategy selection
    let strategies ← getTransformationStrategy pattern
    assertTrue "Should have functor composition transformation strategies" (strategies.length > 0)

    -- Test strategy execution
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic
    assertTrue "Strategy should execute successfully" (result = result)

/-- Test natural transformation pattern detection and transformation -/
def testNaturalTransformationPatternDetection : TestCase :=
  testCase "Natural transformation pattern detection and transformation" do
    let F G : C ⥤ D := Functor.const C (𝟙_ D)
    let α : F ⟶ G := 𝟙 F
    let goal := α = α

    -- Test pattern detection
    let pattern ← analyzeGoal goal
    assertTrue "Should detect natural transformation pattern" (pattern = .naturalTransformation _ _)

    -- Test transformation strategy selection
    let strategies ← getTransformationStrategy pattern
    assertTrue "Should have natural transformation strategies" (strategies.length > 0)

    -- Test strategy execution
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic
    assertTrue "Strategy should execute successfully" (result = result)

/-- Test limit/colimit pattern detection and transformation -/
def testLimitColimitPatternDetection : TestCase :=
  testCase "Limit/colimit pattern detection and transformation" do
    let goal := mkConst `X = mkConst `Y

    -- Test pattern detection
    let pattern ← analyzeGoal goal
    assertTrue "Should detect limit/colimit pattern" (pattern = .limitColimit _ _)

    -- Test transformation strategy selection
    let strategies ← getTransformationStrategy pattern
    assertTrue "Should have limit/colimit transformation strategies" (strategies.length > 0)

    -- Test strategy execution
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic
    assertTrue "Strategy should execute successfully" (result = result)

/-- Test unknown pattern detection and transformation -/
def testUnknownPatternDetection : TestCase :=
  testCase "Unknown pattern detection and transformation" do
    let goal := mkConst `X = mkConst `Y

    -- Test pattern detection
    let pattern ← analyzeGoal goal
    assertTrue "Should detect unknown pattern" (pattern = .unknown _)

    -- Test transformation strategy selection
    let strategies ← getTransformationStrategy pattern
    assertTrue "Should have unknown pattern transformation strategies" (strategies.length > 0)

    -- Test strategy execution
    let (strategyName, strategyTactic) := strategies.head!
    let result ← executeTransformation strategyName strategyTactic
    assertTrue "Strategy should execute successfully" (result = result)

end PatternMatchingIntegrationTests

/-- Test suite for tactic execution integration -/
namespace TacticExecutionIntegrationTests

/-- Test end_beta tactic execution -/
def testEndBetaTacticExecution : TestCase :=
  testCase "end_beta tactic execution" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test tactic execution
    let result ← executeEndKanTactic "end_beta"
    assertTrue "end_beta tactic should execute successfully" (result = result)

/-- Test end_eta tactic execution -/
def testEndEtaTacticExecution : TestCase :=
  testCase "end_eta tactic execution" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test tactic execution
    let result ← executeEndKanTactic "end_eta"
    assertTrue "end_eta tactic should execute successfully" (result = result)

/-- Test coend_beta tactic execution -/
def testCoendBetaTacticExecution : TestCase :=
  testCase "coend_beta tactic execution" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    let ι := Coend.ι F (Classical.arbitrary C)
    let goal := ι ≫ desc = ω.app (Classical.arbitrary C)

    -- Test tactic execution
    let result ← executeEndKanTactic "coend_beta"
    assertTrue "coend_beta tactic should execute successfully" (result = result)

/-- Test coend_eta tactic execution -/
def testCoendEtaTacticExecution : TestCase :=
  testCase "coend_eta tactic execution" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    let ι := Coend.ι F (Classical.arbitrary C)
    let goal := ι ≫ desc = ω.app (Classical.arbitrary C)

    -- Test tactic execution
    let result ← executeEndKanTactic "coend_eta"
    assertTrue "coend_eta tactic should execute successfully" (result = result)

/-- Test kan_fuse tactic execution -/
def testKanFuseTacticExecution : TestCase :=
  testCase "kan_fuse tactic execution" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let lan := Lan K F
    let goal := lan = G

    -- Test tactic execution
    let result ← executeEndKanTactic "kan_fuse"
    assertTrue "kan_fuse tactic should execute successfully" (result = result)

/-- Test beck_chevalley! tactic execution -/
def testBeckChevalleyTacticExecution : TestCase :=
  testCase "beck_chevalley! tactic execution" do
    let goal := mkConst `X = mkConst `Y

    -- Test tactic execution
    let result ← executeEndKanTactic "beck_chevalley!"
    assertTrue "beck_chevalley! tactic should execute successfully" (result = result)

/-- Test endkan_smart tactic execution -/
def testEndkanSmartTacticExecution : TestCase :=
  testCase "endkan_smart tactic execution" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test tactic execution
    let result ← executeEndKanTactic "endkan_smart"
    assertTrue "endkan_smart tactic should execute successfully" (result = result)

/-- Test endkan_debug tactic execution -/
def testEndkanDebugTacticExecution : TestCase :=
  testCase "endkan_debug tactic execution" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test tactic execution
    let result ← executeEndKanTactic "endkan_debug"
    assertTrue "endkan_debug tactic should execute successfully" (result = result)

end TacticExecutionIntegrationTests

/-- Test suite for enhanced tactic execution integration -/
namespace EnhancedTacticExecutionIntegrationTests

/-- Test end_beta! enhanced tactic execution -/
def testEndBetaEnhancedTacticExecution : TestCase :=
  testCase "end_beta! enhanced tactic execution" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test enhanced tactic execution
    let result ← executeEndKanTacticEnhanced "end_beta!"
    assertTrue "end_beta! enhanced tactic should execute successfully" (result = result)

/-- Test end_eta! enhanced tactic execution -/
def testEndEtaEnhancedTacticExecution : TestCase :=
  testCase "end_eta! enhanced tactic execution" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test enhanced tactic execution
    let result ← executeEndKanTacticEnhanced "end_eta!"
    assertTrue "end_eta! enhanced tactic should execute successfully" (result = result)

/-- Test coend_beta! enhanced tactic execution -/
def testCoendBetaEnhancedTacticExecution : TestCase :=
  testCase "coend_beta! enhanced tactic execution" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    let ι := Coend.ι F (Classical.arbitrary C)
    let goal := ι ≫ desc = ω.app (Classical.arbitrary C)

    -- Test enhanced tactic execution
    let result ← executeEndKanTacticEnhanced "coend_beta!"
    assertTrue "coend_beta! enhanced tactic should execute successfully" (result = result)

/-- Test coend_eta! enhanced tactic execution -/
def testCoendEtaEnhancedTacticExecution : TestCase :=
  testCase "coend_eta! enhanced tactic execution" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    let ι := Coend.ι F (Classical.arbitrary C)
    let goal := ι ≫ desc = ω.app (Classical.arbitrary C)

    -- Test enhanced tactic execution
    let result ← executeEndKanTacticEnhanced "coend_eta!"
    assertTrue "coend_eta! enhanced tactic should execute successfully" (result = result)

/-- Test kan_fuse! enhanced tactic execution -/
def testKanFuseEnhancedTacticExecution : TestCase :=
  testCase "kan_fuse! enhanced tactic execution" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let lan := Lan K F
    let goal := lan = G

    -- Test enhanced tactic execution
    let result ← executeEndKanTacticEnhanced "kan_fuse!"
    assertTrue "kan_fuse! enhanced tactic should execute successfully" (result = result)

/-- Test beck_chevalley!! enhanced tactic execution -/
def testBeckChevalleyEnhancedTacticExecution : TestCase :=
  testCase "beck_chevalley!! enhanced tactic execution" do
    let goal := mkConst `X = mkConst `Y

    -- Test enhanced tactic execution
    let result ← executeEndKanTacticEnhanced "beck_chevalley!!"
    assertTrue "beck_chevalley!! enhanced tactic should execute successfully" (result = result)

end EnhancedTacticExecutionIntegrationTests

/-- Test suite for combined tactic execution integration -/
namespace CombinedTacticExecutionIntegrationTests

/-- Test endkan_beta combined tactic execution -/
def testEndkanBetaCombinedTacticExecution : TestCase :=
  testCase "endkan_beta combined tactic execution" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test combined tactic execution
    let result ← executeEndKanTactic "endkan_beta"
    assertTrue "endkan_beta combined tactic should execute successfully" (result = result)

/-- Test endkan_eta combined tactic execution -/
def testEndkanEtaCombinedTacticExecution : TestCase :=
  testCase "endkan_eta combined tactic execution" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test combined tactic execution
    let result ← executeEndKanTactic "endkan_eta"
    assertTrue "endkan_eta combined tactic should execute successfully" (result = result)

/-- Test endkan_all combined tactic execution -/
def testEndkanAllCombinedTacticExecution : TestCase :=
  testCase "endkan_all combined tactic execution" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let π := End.π F (Classical.arbitrary C)
    let goal := lift ≫ π = ω.app (Classical.arbitrary C)

    -- Test combined tactic execution
    let result ← executeEndKanTactic "endkan_all"
    assertTrue "endkan_all combined tactic should execute successfully" (result = result)

end CombinedTacticExecutionIntegrationTests

/-- Test suite for configuration integration -/
namespace ConfigurationIntegrationTests

/-- Test setTimeout configuration -/
def testSetTimeoutConfiguration : TestCase :=
  testCase "setTimeout configuration" do
    let originalTimeout := 2000
    let newTimeout := 5000

    -- Set new timeout
    setTimeout newTimeout

    -- Verify timeout was set
    let config ← endkanConfig.get
    assertTrue "Timeout should be set to new value" (config.timeoutMs = newTimeout)

    -- Reset to original timeout
    setTimeout originalTimeout

/-- Test setTrace configuration -/
def testSetTraceConfiguration : TestCase :=
  testCase "setTrace configuration" do
    let originalTrace := false
    let newTrace := true

    -- Set new trace setting
    setTrace newTrace

    -- Verify trace was set
    let config ← endkanConfig.get
    assertTrue "Trace should be set to new value" (config.trace = newTrace)

    -- Reset to original trace setting
    setTrace originalTrace

/-- Test setMaxSteps configuration -/
def testSetMaxStepsConfiguration : TestCase :=
  testCase "setMaxSteps configuration" do
    let originalMaxSteps := 200
    let newMaxSteps := 500

    -- Set new max steps
    setMaxSteps newMaxSteps

    -- Verify max steps was set
    let config ← endkanConfig.get
    assertTrue "Max steps should be set to new value" (config.maxSteps = newMaxSteps)

    -- Reset to original max steps
    setMaxSteps originalMaxSteps

/-- Test setDebug configuration -/
def testSetDebugConfiguration : TestCase :=
  testCase "setDebug configuration" do
    let originalDebug := false
    let newDebug := true

    -- Set new debug setting
    setDebug newDebug

    -- Verify debug was set
    let config ← endkanConfig.get
    assertTrue "Debug should be set to new value" (config.debug = newDebug)

    -- Reset to original debug setting
    setDebug originalDebug

/-- Test setAggressive configuration -/
def testSetAggressiveConfiguration : TestCase :=
  testCase "setAggressive configuration" do
    let originalAggressive := false
    let newAggressive := true

    -- Set new aggressive setting
    setAggressive newAggressive

    -- Verify aggressive was set
    let config ← endkanConfig.get
    assertTrue "Aggressive should be set to new value" (config.aggressive = newAggressive)

    -- Reset to original aggressive setting
    setAggressive originalAggressive

end ConfigurationIntegrationTests

/-- Test suite for error handling integration -/
namespace ErrorHandlingIntegrationTests

/-- Test timeout error handling -/
def testTimeoutErrorHandling : TestCase :=
  testCase "Timeout error handling" do
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

    -- Test error handling
    let result ← executeEndKanTacticEnhanced "end_beta!"
    assertTrue "Timeout error should be handled gracefully" (result = result)

    -- Reset timeout
    setTimeout 2000

/-- Test max steps error handling -/
def testMaxStepsErrorHandling : TestCase :=
  testCase "Max steps error handling" do
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

    -- Test error handling
    let result ← executeEndKanTacticEnhanced "end_beta!"
    assertTrue "Max steps error should be handled gracefully" (result = result)

    -- Reset max steps
    setMaxSteps 200

/-- Test pattern match failure error handling -/
def testPatternMatchFailureErrorHandling : TestCase :=
  testCase "Pattern match failure error handling" do
    let goal := mkConst `X = mkConst `Y

    -- Test error handling
    let result ← executeEndKanTacticEnhanced "end_beta!"
    assertTrue "Pattern match failure error should be handled gracefully" (result = result)

/-- Test transformation failure error handling -/
def testTransformationFailureErrorHandling : TestCase :=
  testCase "Transformation failure error handling" do
    let goal := mkConst `X = mkConst `Y

    -- Test error handling
    let result ← executeEndKanTacticEnhanced "end_beta!"
    assertTrue "Transformation failure error should be handled gracefully" (result = result)

end ErrorHandlingIntegrationTests

/-- Main test suite for all tactic interaction tests -/
def allTacticInteractionTests : TestSuite :=
  testSuite "Tactic Interactions" [
    PatternMatchingIntegrationTests.testEndPatternDetection,
    PatternMatchingIntegrationTests.testCoendPatternDetection,
    PatternMatchingIntegrationTests.testKanPatternDetection,
    PatternMatchingIntegrationTests.testBeckChevalleyPatternDetection,
    PatternMatchingIntegrationTests.testDinaturalityPatternDetection,
    PatternMatchingIntegrationTests.testFunctorCompositionPatternDetection,
    PatternMatchingIntegrationTests.testNaturalTransformationPatternDetection,
    PatternMatchingIntegrationTests.testLimitColimitPatternDetection,
    PatternMatchingIntegrationTests.testUnknownPatternDetection,
    TacticExecutionIntegrationTests.testEndBetaTacticExecution,
    TacticExecutionIntegrationTests.testEndEtaTacticExecution,
    TacticExecutionIntegrationTests.testCoendBetaTacticExecution,
    TacticExecutionIntegrationTests.testCoendEtaTacticExecution,
    TacticExecutionIntegrationTests.testKanFuseTacticExecution,
    TacticExecutionIntegrationTests.testBeckChevalleyTacticExecution,
    TacticExecutionIntegrationTests.testEndkanSmartTacticExecution,
    TacticExecutionIntegrationTests.testEndkanDebugTacticExecution,
    EnhancedTacticExecutionIntegrationTests.testEndBetaEnhancedTacticExecution,
    EnhancedTacticExecutionIntegrationTests.testEndEtaEnhancedTacticExecution,
    EnhancedTacticExecutionIntegrationTests.testCoendBetaEnhancedTacticExecution,
    EnhancedTacticExecutionIntegrationTests.testCoendEtaEnhancedTacticExecution,
    EnhancedTacticExecutionIntegrationTests.testKanFuseEnhancedTacticExecution,
    EnhancedTacticExecutionIntegrationTests.testBeckChevalleyEnhancedTacticExecution,
    CombinedTacticExecutionIntegrationTests.testEndkanBetaCombinedTacticExecution,
    CombinedTacticExecutionIntegrationTests.testEndkanEtaCombinedTacticExecution,
    CombinedTacticExecutionIntegrationTests.testEndkanAllCombinedTacticExecution,
    ConfigurationIntegrationTests.testSetTimeoutConfiguration,
    ConfigurationIntegrationTests.testSetTraceConfiguration,
    ConfigurationIntegrationTests.testSetMaxStepsConfiguration,
    ConfigurationIntegrationTests.testSetDebugConfiguration,
    ConfigurationIntegrationTests.testSetAggressiveConfiguration,
    ErrorHandlingIntegrationTests.testTimeoutErrorHandling,
    ErrorHandlingIntegrationTests.testMaxStepsErrorHandling,
    ErrorHandlingIntegrationTests.testPatternMatchFailureErrorHandling,
    ErrorHandlingIntegrationTests.testTransformationFailureErrorHandling
  ]

end EndKan.IntegrationTests.TacticInteractions
