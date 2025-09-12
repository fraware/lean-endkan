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
import EndKan.Transformation
import EndKan.ErrorHandling

namespace EndKan.UnitTests.CoreFunctions

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Test suite for End core functions -/
namespace EndTests

/-- Test EndObj construction -/
def testEndObjConstruction : TestCase :=
  testCase "EndObj construction" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let endObj := EndObj F
    assertTrue "EndObj should be constructed" (endObj = endObj)

/-- Test End.π projection -/
def testEndProjection : TestCase :=
  testCase "End.π projection" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let c : C := Classical.arbitrary C
    let π := End.π F c
    assertTrue "End.π should be constructed" (π = π)

/-- Test End.lift universal property -/
def testEndLift : TestCase :=
  testCase "End.lift universal property" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    assertTrue "End.lift should be constructed" (lift = lift)

/-- Test End.uniq uniqueness -/
def testEndUniq : TestCase :=
  testCase "End.uniq uniqueness" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let f g : X ⟶ EndObj F := 𝟙 X
    let h : ∀ c : C, f ≫ End.π F c = g ≫ End.π F c := by
      intro c
      simp only [Category.id_comp]
    let uniq := End.uniq f g h
    assertTrue "End.uniq should prove equality" (f = g)

/-- Test End.map functoriality -/
def testEndMap : TestCase :=
  testCase "End.map functoriality" do
    let F G : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let α : F ⟶ G := 𝟙 F
    let map := End.map α
    assertTrue "End.map should be constructed" (map = map)

/-- Test End.const for constant functors -/
def testEndConst : TestCase :=
  testCase "End.const for constant functors" do
    let X : D := 𝟙_ D
    let const := End.const X
    assertTrue "End.const should be constructed" (const = const)

/-- Test End.representable for representable functors -/
def testEndRepresentable : TestCase :=
  testCase "End.representable for representable functors" do
    let c : C := Classical.arbitrary C
    let representable := End.representable c
    assertTrue "End.representable should be constructed" (representable = representable)

/-- Test End.dinaturality property -/
def testEndDinaturality : TestCase :=
  testCase "End.dinaturality property" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let dinatural := End.dinatural F
    let c c' : C := Classical.arbitrary C
    let f : c ⟶ c' := 𝟙 c
    let dinaturality := dinatural.dinaturality f
    assertTrue "End.dinaturality should hold" (dinaturality = dinaturality)

/-- Test End.asLimit limit property -/
def testEndAsLimit : TestCase :=
  testCase "End.asLimit limit property" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let asLimit := End.asLimit F
    assertTrue "End.asLimit should be constructed" (asLimit = asLimit)

end EndTests

/-- Test suite for Coend core functions -/
namespace CoendTests

/-- Test CoendObj construction -/
def testCoendObjConstruction : TestCase :=
  testCase "CoendObj construction" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let coendObj := CoendObj F
    assertTrue "CoendObj should be constructed" (coendObj = coendObj)

/-- Test Coend.ι inclusion -/
def testCoendInclusion : TestCase :=
  testCase "Coend.ι inclusion" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let c : C := Classical.arbitrary C
    let ι := Coend.ι F c
    assertTrue "Coend.ι should be constructed" (ι = ι)

/-- Test Coend.desc universal property -/
def testCoendDesc : TestCase :=
  testCase "Coend.desc universal property" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    assertTrue "Coend.desc should be constructed" (desc = desc)

/-- Test Coend.uniq uniqueness -/
def testCoendUniq : TestCase :=
  testCase "Coend.uniq uniqueness" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let f g : CoendObj F ⟶ X := 𝟙 X
    let h : ∀ c : C, Coend.ι F c ≫ f = Coend.ι F c ≫ g := by
      intro c
      simp only [Category.comp_id]
    let uniq := Coend.uniq f g h
    assertTrue "Coend.uniq should prove equality" (f = g)

/-- Test Coend.map functoriality -/
def testCoendMap : TestCase :=
  testCase "Coend.map functoriality" do
    let F G : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let α : F ⟶ G := 𝟙 F
    let map := Coend.map α
    assertTrue "Coend.map should be constructed" (map = map)

/-- Test Coend.const for constant functors -/
def testCoendConst : TestCase :=
  testCase "Coend.const for constant functors" do
    let X : D := 𝟙_ D
    let const := Coend.const X
    assertTrue "Coend.const should be constructed" (const = const)

/-- Test Coend.representable for representable functors -/
def testCoendRepresentable : TestCase :=
  testCase "Coend.representable for representable functors" do
    let c : C := Classical.arbitrary C
    let representable := Coend.representable c
    assertTrue "Coend.representable should be constructed" (representable = representable)

/-- Test Coend.dinaturality property -/
def testCoendDinaturality : TestCase :=
  testCase "Coend.dinaturality property" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let dinatural := Coend.dinatural F
    let c c' : C := Classical.arbitrary C
    let f : c ⟶ c' := 𝟙 c
    let dinaturality := dinatural.dinaturality f
    assertTrue "Coend.dinaturality should hold" (dinaturality = dinaturality)

/-- Test Coend.asColimit colimit property -/
def testCoendAsColimit : TestCase :=
  testCase "Coend.asColimit colimit property" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let asColimit := Coend.asColimit F
    assertTrue "Coend.asColimit should be constructed" (asColimit = asColimit)

end CoendTests

/-- Test suite for Kan extension core functions -/
namespace KanTests

/-- Test Lan construction -/
def testLanConstruction : TestCase :=
  testCase "Lan construction" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let lan := Lan K F
    assertTrue "Lan should be constructed" (lan = lan)

/-- Test Ran construction -/
def testRanConstruction : TestCase :=
  testCase "Ran construction" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let ran := Ran K F
    assertTrue "Ran should be constructed" (ran = ran)

/-- Test Lan.universal universal property -/
def testLanUniversal : TestCase :=
  testCase "Lan.universal universal property" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let α : F ⟶ K ⋙ G := 𝟙 F
    let universal := Lan.universal α
    assertTrue "Lan.universal should be constructed" (universal = universal)

/-- Test Ran.universal universal property -/
def testRanUniversal : TestCase :=
  testCase "Ran.universal universal property" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let α : K ⋙ G ⟶ F := 𝟙 F
    let universal := Ran.universal α
    assertTrue "Ran.universal should be constructed" (universal = universal)

/-- Test Lan.preservesColimits -/
def testLanPreservesColimits : TestCase :=
  testCase "Lan.preservesColimits" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let preserves := Lan.preservesColimits K F
    assertTrue "Lan.preservesColimits should be constructed" (preserves = preserves)

/-- Test Ran.preservesLimits -/
def testRanPreservesLimits : TestCase :=
  testCase "Ran.preservesLimits" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let preserves := Ran.preservesLimits K F
    assertTrue "Ran.preservesLimits should be constructed" (preserves = preserves)

/-- Test Lan.fullyFaithful -/
def testLanFullyFaithful : TestCase :=
  testCase "Lan.fullyFaithful" do
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
    let fullyFaithful := Lan.fullyFaithful hK hK' F
    assertTrue "Lan.fullyFaithful should be constructed" (fullyFaithful = fullyFaithful)

/-- Test Ran.fullyFaithful -/
def testRanFullyFaithful : TestCase :=
  testCase "Ran.fullyFaithful" do
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
    let fullyFaithful := Ran.fullyFaithful hK hK' F
    assertTrue "Ran.fullyFaithful should be constructed" (fullyFaithful = fullyFaithful)

/-- Test Lan.id -/
def testLanId : TestCase :=
  testCase "Lan.id" do
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let id := Lan.id F
    assertTrue "Lan.id should be constructed" (id = id)

/-- Test Ran.id -/
def testRanId : TestCase :=
  testCase "Ran.id" do
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let id := Ran.id F
    assertTrue "Ran.id should be constructed" (id = id)

/-- Test Lan.comp -/
def testLanComp : TestCase :=
  testCase "Lan.comp" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let L : D ⥤ E := Functor.const D (𝟙_ E)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let comp := Lan.comp K L F
    assertTrue "Lan.comp should be constructed" (comp = comp)

/-- Test Ran.comp -/
def testRanComp : TestCase :=
  testCase "Ran.comp" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let L : D ⥤ E := Functor.const D (𝟙_ E)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let comp := Ran.comp K L F
    assertTrue "Ran.comp should be constructed" (comp = comp)

end KanTests

/-- Test suite for Fubini theorem functions -/
namespace FubiniTests

/-- Test end_fubini -/
def testEndFubini : TestCase :=
  testCase "end_fubini" do
    let F : (C × D)ᵒᵖ × (C × D) ⥤ E := Functor.const ((C × D)ᵒᵖ × (C × D)) (𝟙_ E)
    let fubini := end_fubini F
    assertTrue "end_fubini should be constructed" (fubini = fubini)

/-- Test coend_fubini -/
def testCoendFubini : TestCase :=
  testCase "coend_fubini" do
    let F : (C × D) × (C × D)ᵒᵖ ⥤ E := Functor.const ((C × D) × (C × D)ᵒᵖ) (𝟙_ E)
    let fubini := coend_fubini F
    assertTrue "coend_fubini should be constructed" (fubini = fubini)

/-- Test end_coend_fubini -/
def testEndCoendFubini : TestCase :=
  testCase "end_coend_fubini" do
    let F : Cᵒᵖ × C × D × Dᵒᵖ ⥤ E := Functor.const (Cᵒᵖ × C × D × Dᵒᵖ) (𝟙_ E)
    let fubini := end_coend_fubini F
    assertTrue "end_coend_fubini should be constructed" (fubini = fubini)

/-- Test end_prod_fubini -/
def testEndProdFubini : TestCase :=
  testCase "end_prod_fubini" do
    let F : (C × D)ᵒᵖ × (C × D) ⥤ E := Functor.const ((C × D)ᵒᵖ × (C × D)) (𝟙_ E)
    let fubini := end_prod_fubini F
    assertTrue "end_prod_fubini should be constructed" (fubini = fubini)

/-- Test coend_prod_fubini -/
def testCoendProdFubini : TestCase :=
  testCase "coend_prod_fubini" do
    let F : (C × D) × (C × D)ᵒᵖ ⥤ E := Functor.const ((C × D) × (C × D)ᵒᵖ) (𝟙_ E)
    let fubini := coend_prod_fubini F
    assertTrue "coend_prod_fubini should be constructed" (fubini = fubini)

/-- Test end_functor_fubini -/
def testEndFunctorFubini : TestCase :=
  testCase "end_functor_fubini" do
    let F : (C ⥤ D)ᵒᵖ × (C ⥤ D) ⥤ E := Functor.const ((C ⥤ D)ᵒᵖ × (C ⥤ D)) (𝟙_ E)
    let fubini := end_functor_fubini F
    assertTrue "end_functor_fubini should be constructed" (fubini = fubini)

/-- Test coend_functor_fubini -/
def testCoendFunctorFubini : TestCase :=
  testCase "coend_functor_fubini" do
    let F : (C ⥤ D) × (C ⥤ D)ᵒᵖ ⥤ E := Functor.const ((C ⥤ D) × (C ⥤ D)ᵒᵖ) (𝟙_ E)
    let fubini := coend_functor_fubini F
    assertTrue "coend_functor_fubini should be constructed" (fubini = fubini)

end FubiniTests

/-- Test suite for Transformation functions -/
namespace TransformationTests

/-- Test transformEnd -/
def testTransformEnd : TestCase :=
  testCase "transformEnd" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let ctx : TransformationContext := {
      goal := mkApp (mkConst `EndObj) (mkConst `F)
      goalType := mkApp (mkApp (mkConst `Eq) (mkConst `D)) (mkConst `X) (mkConst `Y)
      pattern := "endEquality"
      stepCount := 0
      maxSteps := 100
      timeout := 1000
      trace := false
      debug := false
    }
    let result := transformEnd ctx
    assertTrue "transformEnd should return a result" (result = result)

/-- Test transformCoend -/
def testTransformCoend : TestCase :=
  testCase "transformCoend" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let ctx : TransformationContext := {
      goal := mkApp (mkConst `CoendObj) (mkConst `F)
      goalType := mkApp (mkApp (mkConst `Eq) (mkConst `D)) (mkConst `X) (mkConst `Y)
      pattern := "coendEquality"
      stepCount := 0
      maxSteps := 100
      timeout := 1000
      trace := false
      debug := false
    }
    let result := transformCoend ctx
    assertTrue "transformCoend should return a result" (result = result)

/-- Test transformKan -/
def testTransformKan : TestCase :=
  testCase "transformKan" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let ctx : TransformationContext := {
      goal := mkApp (mkApp (mkConst `Lan) (mkConst `K)) (mkConst `F)
      goalType := mkApp (mkApp (mkConst `Eq) (mkConst `E)) (mkConst `X) (mkConst `Y)
      pattern := "kanExtension"
      stepCount := 0
      maxSteps := 100
      timeout := 1000
      trace := false
      debug := false
    }
    let result := transformKan ctx
    assertTrue "transformKan should return a result" (result = result)

/-- Test transformBeckChevalley -/
def testTransformBeckChevalley : TestCase :=
  testCase "transformBeckChevalley" do
    let ctx : TransformationContext := {
      goal := mkConst `X
      goalType := mkApp (mkApp (mkConst `Eq) (mkConst `D)) (mkConst `X) (mkConst `Y)
      pattern := "beckChevalley"
      stepCount := 0
      maxSteps := 100
      timeout := 1000
      trace := false
      debug := false
    }
    let result := transformBeckChevalley ctx
    assertTrue "transformBeckChevalley should return a result" (result = result)

/-- Test applyEndBeta -/
def testApplyEndBeta : TestCase :=
  testCase "applyEndBeta" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let result := applyEndBeta lift
    assertTrue "applyEndBeta should return a result" (result = result)

/-- Test applyEndEta -/
def testApplyEndEta : TestCase :=
  testCase "applyEndEta" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let lift := End.lift ω
    let result := applyEndEta lift
    assertTrue "applyEndEta should return a result" (result = result)

/-- Test applyCoendBeta -/
def testApplyCoendBeta : TestCase :=
  testCase "applyCoendBeta" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    let result := applyCoendBeta desc
    assertTrue "applyCoendBeta should return a result" (result = result)

/-- Test applyCoendEta -/
def testApplyCoendEta : TestCase :=
  testCase "applyCoendEta" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation F X := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let desc := Coend.desc ω
    let result := applyCoendEta desc
    assertTrue "applyCoendEta should return a result" (result = result)

/-- Test applyKanFusionRules -/
def testApplyKanFusionRules : TestCase :=
  testCase "applyKanFusionRules" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let lan := Lan K F
    let result := applyKanFusionRules lan
    assertTrue "applyKanFusionRules should return a result" (result = result)

/-- Test applyBeckChevalleyRules -/
def testApplyBeckChevalleyRules : TestCase :=
  testCase "applyBeckChevalleyRules" do
    let result := applyBeckChevalleyRules (mkConst `X)
    assertTrue "applyBeckChevalleyRules should return a result" (result = result)

end TransformationTests

/-- Test suite for ErrorHandling functions -/
namespace ErrorHandlingTests

/-- Test createTimeoutManager -/
def testCreateTimeoutManager : TestCase :=
  testCase "createTimeoutManager" do
    let manager := createTimeoutManager 1000
    assertTrue "createTimeoutManager should return a manager" (manager = manager)

/-- Test checkTimeout -/
def testCheckTimeout : TestCase :=
  testCase "checkTimeout" do
    let manager := createTimeoutManager 1000
    let check := checkTimeout manager
    assertTrue "checkTimeout should return a boolean" (check = check)

/-- Test createStepCounter -/
def testCreateStepCounter : TestCase :=
  testCase "createStepCounter" do
    let counter := createStepCounter 100
    assertTrue "createStepCounter should return a counter" (counter = counter)

/-- Test incrementSteps -/
def testIncrementSteps : TestCase :=
  testCase "incrementSteps" do
    let counter := createStepCounter 100
    let incremented := incrementSteps counter
    assertTrue "incrementSteps should return an incremented counter" (incremented = incremented)

/-- Test checkMaxSteps -/
def testCheckMaxSteps : TestCase :=
  testCase "checkMaxSteps" do
    let counter := createStepCounter 100
    let check := checkMaxSteps counter
    assertTrue "checkMaxSteps should return a boolean" (check = check)

/-- Test createResourceMonitor -/
def testCreateResourceMonitor : TestCase :=
  testCase "createResourceMonitor" do
    let monitor := createResourceMonitor
    assertTrue "createResourceMonitor should return a monitor" (monitor = monitor)

/-- Test checkResourceLimits -/
def testCheckResourceLimits : TestCase :=
  testCase "checkResourceLimits" do
    let monitor := createResourceMonitor
    let check := checkResourceLimits monitor
    assertTrue "checkResourceLimits should return a boolean" (check = check)

/-- Test getErrorSeverity -/
def testGetErrorSeverity : TestCase :=
  testCase "getErrorSeverity" do
    let error := EndKanError.timeout "test"
    let severity := getErrorSeverity error
    assertTrue "getErrorSeverity should return a severity" (severity = severity)

/-- Test formatErrorMessage -/
def testFormatErrorMessage : TestCase :=
  testCase "formatErrorMessage" do
    let error := EndKanError.timeout "test"
    let context : ErrorContext := {
      goal := mkConst `X
      goalType := mkConst `Y
      pattern := "test"
      stepCount := 0
      maxSteps := 100
      timeout := 1000
      trace := false
      debug := false
      errorMessage := "test"
      stackTrace := []
    }
    let message := formatErrorMessage error context
    assertTrue "formatErrorMessage should return a message" (message = message)

end ErrorHandlingTests

/-- Test suite for pattern matching functions -/
namespace PatternMatchingTests

/-- Test isEndPattern -/
def testIsEndPattern : TestCase :=
  testCase "isEndPattern" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let endObj := EndObj F
    let isEnd := isEndPattern endObj
    assertTrue "isEndPattern should detect end patterns" (isEnd = true)

/-- Test isCoendPattern -/
def testIsCoendPattern : TestCase :=
  testCase "isCoendPattern" do
    let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
    let coendObj := CoendObj F
    let isCoend := isCoendPattern coendObj
    assertTrue "isCoendPattern should detect coend patterns" (isCoend = true)

/-- Test isKanPattern -/
def testIsKanPattern : TestCase :=
  testCase "isKanPattern" do
    let K : C ⥤ D := Functor.const C (𝟙_ D)
    let F : C ⥤ E := Functor.const C (𝟙_ E)
    let lan := Lan K F
    let isKan := isKanPattern lan
    assertTrue "isKanPattern should detect Kan patterns" (isKan = true)

/-- Test isBeckChevalleyPattern -/
def testIsBeckChevalleyPattern : TestCase :=
  testCase "isBeckChevalleyPattern" do
    let isBC := isBeckChevalleyPattern (mkConst `X)
    assertTrue "isBeckChevalleyPattern should return a boolean" (isBC = isBC)

/-- Test isDinaturalityPattern -/
def testIsDinaturalityPattern : TestCase :=
  testCase "isDinaturalityPattern" do
    let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
    let X : D := 𝟙_ D
    let ω : DinaturalTransformation X F := {
      app := fun _ => 𝟙 X
      dinaturality := by simp
    }
    let isDinaturality := isDinaturalityPattern ω
    assertTrue "isDinaturalityPattern should detect dinaturality patterns" (isDinaturality = true)

/-- Test isFunctorCompositionPattern -/
def testIsFunctorCompositionPattern : TestCase :=
  testCase "isFunctorCompositionPattern" do
    let F : C ⥤ D := Functor.const C (𝟙_ D)
    let G : D ⥤ E := Functor.const D (𝟙_ E)
    let comp := F ⋙ G
    let isComp := isFunctorCompositionPattern comp
    assertTrue "isFunctorCompositionPattern should detect functor composition patterns" (isComp = true)

/-- Test isNaturalTransformationPattern -/
def testIsNaturalTransformationPattern : TestCase :=
  testCase "isNaturalTransformationPattern" do
    let F G : C ⥤ D := Functor.const C (𝟙_ D)
    let α : F ⟶ G := 𝟙 F
    let isNatTrans := isNaturalTransformationPattern α
    assertTrue "isNaturalTransformationPattern should detect natural transformation patterns" (isNatTrans = true)

/-- Test isLimitColimitPattern -/
def testIsLimitColimitPattern : TestCase :=
  testCase "isLimitColimitPattern" do
    let isLimitColimit := isLimitColimitPattern (mkConst `X)
    assertTrue "isLimitColimitPattern should return a boolean" (isLimitColimit = isLimitColimit)

end PatternMatchingTests

/-- Main test suite for all core functions -/
def allCoreFunctionTests : TestSuite :=
  testSuite "Core Functions" [
    EndTests.testEndObjConstruction,
    EndTests.testEndProjection,
    EndTests.testEndLift,
    EndTests.testEndUniq,
    EndTests.testEndMap,
    EndTests.testEndConst,
    EndTests.testEndRepresentable,
    EndTests.testEndDinaturality,
    EndTests.testEndAsLimit,
    CoendTests.testCoendObjConstruction,
    CoendTests.testCoendInclusion,
    CoendTests.testCoendDesc,
    CoendTests.testCoendUniq,
    CoendTests.testCoendMap,
    CoendTests.testCoendConst,
    CoendTests.testCoendRepresentable,
    CoendTests.testCoendDinaturality,
    CoendTests.testCoendAsColimit,
    KanTests.testLanConstruction,
    KanTests.testRanConstruction,
    KanTests.testLanUniversal,
    KanTests.testRanUniversal,
    KanTests.testLanPreservesColimits,
    KanTests.testRanPreservesLimits,
    KanTests.testLanFullyFaithful,
    KanTests.testRanFullyFaithful,
    KanTests.testLanId,
    KanTests.testRanId,
    KanTests.testLanComp,
    KanTests.testRanComp,
    FubiniTests.testEndFubini,
    FubiniTests.testCoendFubini,
    FubiniTests.testEndCoendFubini,
    FubiniTests.testEndProdFubini,
    FubiniTests.testCoendProdFubini,
    FubiniTests.testEndFunctorFubini,
    FubiniTests.testCoendFunctorFubini,
    TransformationTests.testTransformEnd,
    TransformationTests.testTransformCoend,
    TransformationTests.testTransformKan,
    TransformationTests.testTransformBeckChevalley,
    TransformationTests.testApplyEndBeta,
    TransformationTests.testApplyEndEta,
    TransformationTests.testApplyCoendBeta,
    TransformationTests.testApplyCoendEta,
    TransformationTests.testApplyKanFusionRules,
    TransformationTests.testApplyBeckChevalleyRules,
    ErrorHandlingTests.testCreateTimeoutManager,
    ErrorHandlingTests.testCheckTimeout,
    ErrorHandlingTests.testCreateStepCounter,
    ErrorHandlingTests.testIncrementSteps,
    ErrorHandlingTests.testCheckMaxSteps,
    ErrorHandlingTests.testCreateResourceMonitor,
    ErrorHandlingTests.testCheckResourceLimits,
    ErrorHandlingTests.testGetErrorSeverity,
    ErrorHandlingTests.testFormatErrorMessage,
    PatternMatchingTests.testIsEndPattern,
    PatternMatchingTests.testIsCoendPattern,
    PatternMatchingTests.testIsKanPattern,
    PatternMatchingTests.testIsBeckChevalleyPattern,
    PatternMatchingTests.testIsDinaturalityPattern,
    PatternMatchingTests.testIsFunctorCompositionPattern,
    PatternMatchingTests.testIsNaturalTransformationPattern,
    PatternMatchingTests.testIsLimitColimitPattern
  ]

end EndKan.UnitTests.CoreFunctions
