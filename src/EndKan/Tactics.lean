import Mathlib.Tactic.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.Tactic.CategoryTheory.Bicategory
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Tactic.CategoryTheory.Simpa
import Mathlib.Tactic.CategoryTheory.Tidy
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.Tactic.CategoryTheory.Reassoc
import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Kan.Core
import EndKan.Kan.BeckChevalley
import EndKan.Transformation
import EndKan.ErrorHandling

namespace EndKan.Tactics

open CategoryTheory
open CategoryTheory.Limits
open Lean Elab Tactic Meta

/-- Configuration options for EndKan tactics -/
structure EndKanConfig where
  timeoutMs : Nat := 2000
  trace : Bool := false
  maxSteps : Nat := 200
  debug : Bool := false
  aggressive : Bool := false

/-- Global configuration for EndKan tactics -/
def endkanConfig : IO.Ref EndKanConfig := IO.mkRef {}

/-- Set timeout for EndKan tactics -/
def setTimeout (ms : Nat) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with timeoutMs := ms }

/-- Set tracing for EndKan tactics -/
def setTrace (b : Bool) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with trace := b }

/-- Set maximum steps for EndKan tactics -/
def setMaxSteps (n : Nat) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with maxSteps := n }

/-- Set debug mode for EndKan tactics -/
def setDebug (b : Bool) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with debug := b }

/-- Set aggressive mode for EndKan tactics -/
def setAggressive (b : Bool) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with aggressive := b }

/-- Error types for EndKan tactics -/
inductive EndKanError where
  | timeout : String → EndKanError
  | maxStepsReached : String → EndKanError
  | patternMatchFailed : String → EndKanError
  | transformationFailed : String → EndKanError
  | invalidGoal : String → EndKanError
  | dependencyMissing : String → EndKanError

/-- Exception wrapper for EndKan errors -/
def EndKanException (msg : String) : Exception :=
  Exception.internal `EndKanException msg

/-- Goal pattern matching for EndKan tactics -/
inductive GoalPattern where
  | endEquality : Expr → Expr → GoalPattern
  | coendEquality : Expr → Expr → GoalPattern
  | kanExtension : Expr → Expr → GoalPattern
  | beckChevalley : Expr → Expr → GoalPattern
  | dinaturality : Expr → Expr → GoalPattern
  | functorComposition : Expr → Expr → GoalPattern
  | naturalTransformation : Expr → Expr → GoalPattern
  | limitColimit : Expr → Expr → GoalPattern
  | unknown : Expr → GoalPattern

/-- Analyze goal to determine pattern -/
def analyzeGoal (goal : Expr) : MetaM GoalPattern := do
  let goalType ← inferType goal
  match goalType with
  | .app (.app (.const `Eq _) _) lhs rhs => do
    if isEndPattern lhs || isEndPattern rhs then
      return .endEquality lhs rhs
    else if isCoendPattern lhs || isCoendPattern rhs then
      return .coendEquality lhs rhs
    else if isKanPattern lhs || isKanPattern rhs then
      return .kanExtension lhs rhs
    else if isBeckChevalleyPattern lhs || isBeckChevalleyPattern rhs then
      return .beckChevalley lhs rhs
    else if isDinaturalityPattern lhs || isDinaturalityPattern rhs then
      return .dinaturality lhs rhs
    else if isFunctorCompositionPattern lhs || isFunctorCompositionPattern rhs then
      return .functorComposition lhs rhs
    else if isNaturalTransformationPattern lhs || isNaturalTransformationPattern rhs then
      return .naturalTransformation lhs rhs
    else if isLimitColimitPattern lhs || isLimitColimitPattern rhs then
      return .limitColimit lhs rhs
    else
      return .unknown goalType
  | _ => return .unknown goalType

/-- Check if expression is an end pattern -/
def isEndPattern (e : Expr) : Bool :=
  match e with
  | .app (.const `EndKan.End.EndObj _) _ => true
  | .app (.app (.const `EndKan.End.End.π _) _) _ => true
  | .app (.app (.app (.const `EndKan.End.End.lift _) _) _) _ => true
  | .app (.app (.const `EndKan.End.End.map _) _) _ => true
  | _ => false

/-- Check if expression is a coend pattern -/
def isCoendPattern (e : Expr) : Bool :=
  match e with
  | .app (.const `EndKan.Coend.CoendObj _) _ => true
  | .app (.app (.const `EndKan.Coend.Coend.ι _) _) _ => true
  | .app (.app (.app (.const `EndKan.Coend.Coend.desc _) _) _) _ => true
  | .app (.app (.const `EndKan.Coend.Coend.map _) _) _ => true
  | _ => false

/-- Check if expression is a Kan extension pattern -/
def isKanPattern (e : Expr) : Bool :=
  match e with
  | .app (.app (.const `EndKan.Kan.Lan _) _) _ => true
  | .app (.app (.const `EndKan.Kan.Ran _) _) _ => true
  | .app (.app (.app (.const `EndKan.Kan.Lan.universal _) _) _) _ => true
  | .app (.app (.app (.const `EndKan.Kan.Ran.universal _) _) _) _ => true
  | _ => false

/-- Check if expression is a Beck-Chevalley pattern -/
def isBeckChevalleyPattern (e : Expr) : Bool :=
  match e with
  | .app (.app (.app (.app (.const `EndKan.Kan.BeckChevalley.Square _) _) _) _) _ => true
  | .app (.const `EndKan.Kan.BeckChevalley.beckChevalleyIso _) _ => true
  | .app (.const `EndKan.Kan.BeckChevalley.beckChevalleyPullback _) _ => true
  | .app (.const `EndKan.Kan.BeckChevalley.beckChevalleyFullyFaithful _) _ => true
  | .app (.const `EndKan.Kan.BeckChevalley.beckChevalleyExact _) _ => true
  | _ => false

/-- Check if expression is a dinaturality pattern -/
def isDinaturalityPattern (e : Expr) : Bool :=
  match e with
  | .app (.app (.const `EndKan.End.DinaturalTransformation _) _) _ => true
  | .app (.app (.const `EndKan.Coend.DinaturalTransformation _) _) _ => true
  | _ => false

/-- Check if expression is a functor composition pattern -/
def isFunctorCompositionPattern (e : Expr) : Bool :=
  match e with
  | .app (.app (.const `CategoryTheory.Functor.comp _) _) _ => true
  | .app (.app (.const `CategoryTheory.Functor.map _) _) _ => true
  | _ => false

/-- Check if expression is a natural transformation pattern -/
def isNaturalTransformationPattern (e : Expr) : Bool :=
  match e with
  | .app (.app (.const `CategoryTheory.NatTrans _) _) _ => true
  | .app (.app (.const `CategoryTheory.NatTrans.app _) _) _ => true
  | _ => false

/-- Check if expression is a limit/colimit pattern -/
def isLimitColimitPattern (e : Expr) : Bool :=
  match e with
  | .app (.const `CategoryTheory.Limits.LimitCone _) _ => true
  | .app (.const `CategoryTheory.Limits.ColimitCocone _) _ => true
  | .app (.const `CategoryTheory.Limits.IsLimit _) _ => true
  | .app (.const `CategoryTheory.Limits.IsColimit _) _ => true
  | _ => false

/-- Transformation strategies for different patterns -/
def getTransformationStrategy (pattern : GoalPattern) : List (String × TacticM Unit) :=
  match pattern with
  | .endEquality _ _ => [
      ("end_beta", evalTactic (← `(tactic| simp only [EndKan.End.end_beta, EndKan.End.end_π_beta, EndKan.End.end_map_beta]))),
      ("end_eta", evalTactic (← `(tactic| simp only [EndKan.End.end_eta, EndKan.End.end_π_eta, EndKan.End.end_map_eta]))),
      ("end_comp", evalTactic (← `(tactic| simp only [EndKan.End.end_comp, EndKan.End.end_prod, EndKan.End.end_op]))),
      ("end_universal", evalTactic (← `(tactic| simp only [EndKan.End.End.lift_π, EndKan.End.End.uniq])))
    ]
  | .coendEquality _ _ => [
      ("coend_beta", evalTactic (← `(tactic| simp only [EndKan.Coend.coend_beta, EndKan.Coend.coend_ι_beta, EndKan.Coend.coend_map_beta]))),
      ("coend_eta", evalTactic (← `(tactic| simp only [EndKan.Coend.coend_eta, EndKan.Coend.coend_ι_eta, EndKan.Coend.coend_map_eta]))),
      ("coend_comp", evalTactic (← `(tactic| simp only [EndKan.Coend.coend_comp, EndKan.Coend.coend_coprod, EndKan.Coend.coend_op]))),
      ("coend_universal", evalTactic (← `(tactic| simp only [EndKan.Coend.Coend.desc_ι, EndKan.Coend.Coend.uniq])))
    ]
  | .kanExtension _ _ => [
      ("kan_fuse", evalTactic (← `(tactic| simp only [EndKan.Kan.Lan.fullyFaithful, EndKan.Kan.Ran.fullyFaithful, EndKan.Kan.Lan.id, EndKan.Kan.Ran.id, EndKan.Kan.Lan.comp, EndKan.Kan.Ran.comp]))),
      ("kan_universal", evalTactic (← `(tactic| simp only [EndKan.Kan.Lan.universal, EndKan.Kan.Ran.universal]))),
      ("kan_preserves", evalTactic (← `(tactic| simp only [EndKan.Kan.Lan.preservesColimits, EndKan.Kan.Ran.preservesLimits])))
    ]
  | .beckChevalley _ _ => [
      ("beck_chevalley", evalTactic (← `(tactic| simp only [EndKan.Kan.BeckChevalley.beckChevalleyIso, EndKan.Kan.BeckChevalley.beckChevalleyPullback, EndKan.Kan.BeckChevalley.beckChevalleyFullyFaithful, EndKan.Kan.BeckChevalley.beckChevalleyExact]))),
      ("beck_chevalley_comp", evalTactic (← `(tactic| simp only [EndKan.Kan.BeckChevalley.beckChevalleyComp, EndKan.Kan.BeckChevalley.beckChevalleyOp, EndKan.Kan.BeckChevalley.beckChevalleyProd, EndKan.Kan.BeckChevalley.beckChevalleyFunctor])))
    ]
  | .dinaturality _ _ => [
      ("dinaturality", evalTactic (← `(tactic| simp only [EndKan.End.DinaturalTransformation.dinaturality, EndKan.Coend.DinaturalTransformation.dinaturality]))),
      ("dinaturality_app", evalTactic (← `(tactic| simp only [EndKan.End.DinaturalTransformation.app, EndKan.Coend.DinaturalTransformation.app])))
    ]
  | .functorComposition _ _ => [
      ("functor_comp", evalTactic (← `(tactic| simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]))),
      ("functor_naturality", evalTactic (← `(tactic| simp only [CategoryTheory.Functor.naturality])))
    ]
  | .naturalTransformation _ _ => [
      ("nat_trans", evalTactic (← `(tactic| simp only [CategoryTheory.NatTrans.naturality, CategoryTheory.NatTrans.app]))),
      ("nat_trans_comp", evalTactic (← `(tactic| simp only [CategoryTheory.NatTrans.comp_app, CategoryTheory.NatTrans.id_app])))
    ]
  | .limitColimit _ _ => [
      ("limit_colimit", evalTactic (← `(tactic| simp only [CategoryTheory.Limits.IsLimit.fac, CategoryTheory.Limits.IsColimit.fac, CategoryTheory.Limits.IsLimit.uniq, CategoryTheory.Limits.IsColimit.uniq]))),
      ("limit_colimit_preserves", evalTactic (← `(tactic| simp only [CategoryTheory.Limits.PreservesColimits.preserves, CategoryTheory.Limits.PreservesLimits.preserves])))
    ]
  | .unknown _ => [
      ("general_simp", evalTactic (← `(tactic| simp))),
      ("general_simp_all", evalTactic (← `(tactic| simp_all))),
      ("general_rfl", evalTactic (← `(tactic| rfl))),
      ("general_assumption", evalTactic (← `(tactic| assumption)))
    ]

/-- Execute transformation with error handling and timeout -/
def executeTransformation (strategy : String) (tactic : TacticM Unit) : TacticM Unit := do
  let config ← endkanConfig.get
  try
  withOptions (fun opts => opts.set `maxHeartbeats config.timeoutMs) do
      tactic
  catch e =>
    if config.debug then
      logInfo s!"EndKan: Strategy '{strategy}' failed: {e.message}"
    throw e

/-- Main tactic execution with pattern matching and error handling -/
def executeEndKanTactic (tacticName : String) : TacticM Unit := do
  let config ← endkanConfig.get
  let goal ← getMainGoal
  let goalType ← inferType goal

  if config.trace then
    logInfo s!"EndKan: Analyzing goal: {goalType}"

  let pattern ← analyzeGoal goal
  let strategies ← getTransformationStrategy pattern

  if config.trace then
    logInfo s!"EndKan: Detected pattern: {pattern}, found {strategies.length} strategies"

  let mut success := false
  let mut stepCount := 0

  for (strategyName, strategyTactic) in strategies do
    if stepCount >= config.maxSteps then
      throw (EndKanException s!"EndKan: Maximum steps ({config.maxSteps}) reached")

    if config.trace then
      logInfo s!"EndKan: Trying strategy '{strategyName}'"

    try
      executeTransformation strategyName strategyTactic
      success := true
      if config.trace then
        logInfo s!"EndKan: Strategy '{strategyName}' succeeded"
      break
    catch e =>
      if config.debug then
        logInfo s!"EndKan: Strategy '{strategyName}' failed: {e.message}"
      stepCount := stepCount + 1
      continue

  if not success then
    throw (EndKanException s!"EndKan: All strategies failed for pattern {pattern}")

/-- Tactic entry with extra error detail -/
def executeEndKanTacticEnhanced (tacticName : String) : TacticM Unit := do
  let config ← endkanConfig.get
  let goal ← getMainGoal
  let goalType ← inferType goal

  if config.trace then
    logInfo s!"EndKan: Analyzing goal: {goalType}"

  let pattern ← analyzeGoal goal
  let strategies ← getTransformationStrategy pattern

  if config.trace then
    logInfo s!"EndKan: Detected pattern: {pattern}, found {strategies.length} strategies"

  let mut success := false
  let mut stepCount := 0

  for (strategyName, strategyTactic) in strategies do
    if stepCount >= config.maxSteps then
      let context : ErrorHandling.ErrorContext := {
        goal,
        goalType,
        pattern := toString pattern,
        stepCount,
        maxSteps := config.maxSteps,
        timeout := config.timeoutMs,
        trace := config.trace,
        debug := config.debug,
        errorMessage := s!"Maximum steps ({config.maxSteps}) reached",
        stackTrace := []
      }
      ErrorHandling.handleEndKanError (.maxStepsReached s!"Maximum steps ({config.maxSteps}) reached") context
      return

    if config.trace then
      logInfo s!"EndKan: Trying strategy '{strategyName}'"

    try
      ErrorHandling.safeExecute (executeTransformation strategyName strategyTactic) config.timeoutMs config.maxSteps config.debug
      success := true
      if config.trace then
        logInfo s!"EndKan: Strategy '{strategyName}' succeeded"
      break
    catch e =>
      if config.debug then
        logInfo s!"EndKan: Strategy '{strategyName}' failed: {e.message}"
      stepCount := stepCount + 1
      continue

  if not success then
    let context : ErrorHandling.ErrorContext := {
      goal,
      goalType,
      pattern := toString pattern,
      stepCount,
      maxSteps := config.maxSteps,
      timeout := config.timeoutMs,
      trace := config.trace,
      debug := config.debug,
      errorMessage := s!"All strategies failed for pattern {pattern}",
      stackTrace := []
    }
    ErrorHandling.handleEndKanError (.transformationFailed s!"All strategies failed for pattern {pattern}") context

/-- End β-reduction tactic with pattern matching -/
elab "end_beta" : tactic => do
  executeEndKanTactic "end_beta"

/-- End η-expansion tactic with pattern matching -/
elab "end_eta" : tactic => do
  executeEndKanTactic "end_eta"

/-- Coend β-reduction tactic with pattern matching -/
elab "coend_beta" : tactic => do
  executeEndKanTactic "coend_beta"

/-- Coend η-expansion tactic with pattern matching -/
elab "coend_eta" : tactic => do
  executeEndKanTactic "coend_eta"

/-- Kan fusion tactic with pattern matching -/
elab "kan_fuse" : tactic => do
  executeEndKanTactic "kan_fuse"

/-- Beck-Chevalley tactic with pattern matching -/
elab "beck_chevalley!" : tactic => do
  executeEndKanTactic "beck_chevalley!"

/-- Tactics with extra error detail -/
elab "end_beta!" : tactic => do
  executeEndKanTacticEnhanced "end_beta!"

elab "end_eta!" : tactic => do
  executeEndKanTacticEnhanced "end_eta!"

elab "coend_beta!" : tactic => do
  executeEndKanTacticEnhanced "coend_beta!"

elab "coend_eta!" : tactic => do
  executeEndKanTacticEnhanced "coend_eta!"

elab "kan_fuse!" : tactic => do
  executeEndKanTacticEnhanced "kan_fuse!"

elab "beck_chevalley!!" : tactic => do
  executeEndKanTacticEnhanced "beck_chevalley!!"

/-- End β-reduction in term mode -/
macro "by end_beta" : term => `(by end_beta)

/-- End η-expansion in term mode -/
macro "by end_eta" : term => `(by end_eta)

/-- Coend β-reduction in term mode -/
macro "by coend_beta" : term => `(by coend_beta)

/-- Coend η-expansion in term mode -/
macro "by coend_eta" : term => `(by coend_eta)

/-- Kan fusion in term mode -/
macro "by kan_fuse" : term => `(by kan_fuse)

/-- Beck-Chevalley in term mode -/
macro "by beck_chevalley!" : term => `(by beck_chevalley!)

/-- Combined end/coend tactics -/
elab "endkan_beta" : tactic => do
  evalTactic (← `(tactic| end_beta <;> coend_beta))

/-- Combined end/coend tactics -/
elab "endkan_eta" : tactic => do
  evalTactic (← `(tactic| end_eta <;> coend_eta))

/-- Combined end/coend tactics in term mode -/
macro "by endkan_beta" : term => `(by endkan_beta)

/-- Combined end/coend tactics in term mode -/
macro "by endkan_eta" : term => `(by endkan_eta)

/-- Combined all tactics -/
elab "endkan_all" : tactic => do
  evalTactic (← `(tactic| endkan_beta <;> endkan_eta <;> kan_fuse <;> beck_chevalley!))

/-- Combined all tactics in term mode -/
macro "by endkan_all" : term => `(by endkan_all)

/-- Smart tactic that automatically detects and applies appropriate transformations -/
elab "endkan_smart" : tactic => do
  executeEndKanTactic "endkan_smart"

/-- Smart tactic in term mode -/
macro "by endkan_smart" : term => `(by endkan_smart)

/-- Debug tactic that shows what pattern was detected -/
elab "endkan_debug" : tactic => do
  let config ← endkanConfig.get
  let goal ← getMainGoal
  let goalType ← inferType goal
  let pattern ← analyzeGoal goal

  logInfo s!"EndKan Debug: Goal type: {goalType}"
  logInfo s!"EndKan Debug: Detected pattern: {pattern}"

  let strategies ← getTransformationStrategy pattern
  logInfo s!"EndKan Debug: Available strategies: {strategies.map (·.1)}"

  executeEndKanTactic "endkan_debug"

/-- Debug tactic in term mode -/
macro "by endkan_debug" : term => `(by endkan_debug)

end EndKan.Tactics
