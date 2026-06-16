import Mathlib.Tactic.Basic
import Mathlib.Tactic.CategoryTheory.Reassoc
import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Kan.Core
import EndKan.Kan.BeckChevalley
import EndKan.ErrorHandling
import EndKan.Automation.PatternCore

namespace EndKan.Tactics

open Lean Elab Tactic Meta

structure EndKanConfig where
  timeoutMs : Nat := 2000
  trace : Bool := false
  maxSteps : Nat := 200
  debug : Bool := false
  aggressive : Bool := false
  deriving Inhabited

def defaultConfig : EndKanConfig :=
  { timeoutMs := 2000, trace := false, maxSteps := 200, debug := false, aggressive := false }

initialize endkanConfig : IO.Ref EndKanConfig ← IO.mkRef defaultConfig

def setTimeout (ms : Nat) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with timeoutMs := ms }

def setTrace (b : Bool) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with trace := b }

def setMaxSteps (n : Nat) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with maxSteps := n }

def setDebug (b : Bool) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with debug := b }

def setAggressive (b : Bool) : IO Unit := do
  let config ← endkanConfig.get
  endkanConfig.set { config with aggressive := b }

def executeEndKanTactic (name : String) : TacticM Unit :=
  EndKan.Core.executeTactic name

elab "end_beta" : tactic => do
  try evalTactic (← `(tactic| simp only [EndKan.End.end_beta, EndKan.End.lift_π]))
  catch _ => executeEndKanTactic "end_beta"

elab "end_eta" : tactic => do
  try evalTactic (← `(tactic| simp only [EndKan.End.end_eta]))
  catch _ => executeEndKanTactic "end_eta"

elab "coend_beta" : tactic => do
  try evalTactic (← `(tactic| simp only [EndKan.Coend.coend_beta, EndKan.Coend.desc_ι]))
  catch _ => executeEndKanTactic "coend_beta"

elab "coend_ι_beta" : tactic => do
  try evalTactic (← `(tactic| simp only [EndKan.Coend.coend_ι_beta, EndKan.Coend.ι_dinatural]))
  catch _ => executeEndKanTactic "coend_ι_beta"

elab "coend_eta" : tactic => do
  try evalTactic (← `(tactic| simp only [EndKan.Coend.coend_eta]))
  catch _ => executeEndKanTactic "coend_eta"

elab "endkan_smart" : tactic => do
  evalTactic (← `(tactic|
    first
    | end_beta
    | end_eta
    | coend_beta
    | coend_ι_beta
    | coend_eta
    | simp))

elab "endkan_debug" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let goalType ← mvarId.getType
    logInfo m!"EndKan debug goal: {goalType}"
  executeEndKanTactic "endkan_debug"

elab "beck_chevalley!" : tactic => do
  try evalTactic (← `(tactic|
    first
    | exact EndKan.Kan.BeckChevalley.beckChevalleyPullback
    | simp only [EndKan.Kan.BeckChevalley.beckChevalleyIso,
                 EndKan.Kan.BeckChevalley.beckChevalleyPullback,
                 EndKan.Kan.BeckChevalley.beckChevalleyFullyFaithful,
                 EndKan.Kan.BeckChevalley.beckChevalleyExact]))
  catch _ => executeEndKanTactic "beck_chevalley!"

end EndKan.Tactics
