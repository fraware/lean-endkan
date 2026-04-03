import Lake
open Lake DSL

package «lean-endkan» where
  -- Fixed Mathlib version; change together with `lean-toolchain` when upgrading Lean.
  require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib «EndKan» where

lean_lib «EndKan.ProductionBenchmarks» where

lean_lib «EndKan.Telemetry» where

lean_lib «EndKan.Optimization» where

lean_lib «EndKan.Configuration» where

lean_lib «EndKan.Monitoring» where

lean_exe «test» where
  root := `Test

lean_exe «run_tests» where
  root := `SmokeTests

lean_exe «run_production_tests» where
  root := `RunProductionTests

lean_exe «deploy_production» where
  root := `DeployProduction

lean_exe «test-runner» where
  root := `EndKan.TestRunner
  supportInterpreter := true
