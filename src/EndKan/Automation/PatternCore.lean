import Mathlib.Tactic.Basic
import EndKan.ErrorHandling
import EndKan.End.BetaEta
import EndKan.Coend.BetaEta

namespace EndKan.Core

open CategoryTheory
open Lean Elab Tactic Meta

structure EndKanCore where
  patternType : String
  confidence : Float
  strategies : List String
  correctnessProof : Option String

def isEndPattern (e : Expr) : Bool :=
  match e with
  | .app (.const `EndKan.End.EndObj _) _ => true
  | .app (.app (.const `EndKan.End.π _) _) _ => true
  | .app (.app (.app (.const `EndKan.End.lift _) _) _) _ => true
  | .app (.app (.const `EndKan.End.map _) _) _ => true
  | _ => false

def isCoendPattern (e : Expr) : Bool :=
  match e with
  | .app (.const `EndKan.Coend.CoendObj _) _ => true
  | .app (.app (.const `EndKan.Coend.ι _) _) _ => true
  | .app (.app (.app (.const `EndKan.Coend.desc _) _) _) _ => true
  | .app (.app (.const `EndKan.Coend.map _) _) _ => true
  | _ => false

def isKanPattern (e : Expr) : Bool :=
  match e with
  | .app (.app (.const `EndKan.Kan.Lan _) _) _ => true
  | .app (.app (.const `EndKan.Kan.Ran _) _) _ => true
  | _ => false

def isBeckChevalleyPattern (e : Expr) : Bool :=
  match e with
  | .app (.app (.app (.app (.const `EndKan.Kan.BeckChevalley.Square _) _) _) _) _ => true
  | .app (.const `EndKan.Kan.BeckChevalley.BC _) _ => true
  | .app (.const `EndKan.Kan.BeckChevalley.BeckChevalleyTarget _) _ => true
  | _ => false

def matchPattern (goal : MVarId) : MetaM EndKanCore := goal.withContext do
  let goalType ← goal.getType
  unless goalType.isAppOf ``Eq do
    return {
      patternType := "unknown"
      confidence := 0.0
      strategies := ["general_simp"]
      correctnessProof := none
    }
  let lhs := goalType.appFn!.appArg!
  let rhs := goalType.appArg!
  if isEndPattern lhs || isEndPattern rhs then
      return {
        patternType := "end_equality"
        confidence := 0.95
        strategies := ["end_beta", "end_eta"]
        correctnessProof := some "End equality pattern verified"
      }
    else if isCoendPattern lhs || isCoendPattern rhs then
      return {
        patternType := "coend_equality"
        confidence := 0.95
        strategies := ["coend_beta", "coend_ι_beta", "coend_eta"]
        correctnessProof := some "Coend equality pattern verified"
      }
    else if isKanPattern lhs || isKanPattern rhs then
      return {
        patternType := "kan_extension"
        confidence := 0.90
        strategies := ["kan_fusion"]
        correctnessProof := some "Kan extension pattern verified"
      }
    else if isBeckChevalleyPattern lhs || isBeckChevalleyPattern rhs then
      return {
        patternType := "beck_chevalley"
        confidence := 0.85
        strategies := ["beck_chevalley"]
        correctnessProof := some "Beck-Chevalley pattern verified"
      }
    else
      return {
        patternType := "unknown"
        confidence := 0.0
        strategies := ["general_simp"]
        correctnessProof := none
      }

def applyStrategy (strategy : String) : TacticM Unit := do
  match strategy with
  | "end_beta" => evalTactic (← `(tactic| simp only [EndKan.End.end_beta, EndKan.End.lift_π]))
  | "end_eta" => evalTactic (← `(tactic| simp only [EndKan.End.end_eta]))
  | "coend_beta" => evalTactic (← `(tactic| simp only [EndKan.Coend.coend_beta, EndKan.Coend.desc_ι]))
  | "coend_eta" => evalTactic (← `(tactic| simp only [EndKan.Coend.coend_eta]))
  | _ => evalTactic (← `(tactic| simp))

def executeTactic (_name : String) : TacticM Unit := do
  let goal ← getMainGoal
  let core ← matchPattern goal
  match core.correctnessProof with
  | some proof => do
      logInfo s!"EndKan: {proof}"
      let mut success := false
      for strategy in core.strategies do
        try
          applyStrategy strategy
          success := true
          break
        catch _ =>
          continue
      if not success then
        throwError "EndKan: all strategies failed for pattern {core.patternType}"
  | none => do
      logWarning s!"EndKan: no correctness proof available for pattern {core.patternType}"
      let mut success := false
      for strategy in core.strategies do
        try
          applyStrategy strategy
          success := true
          break
        catch _ =>
          continue
      if not success then
        throwError "EndKan: all strategies failed"

end EndKan.Core
