import Lake
open Lake DSL

package «lean-endkan» where
  srcDir := "src"
  -- Audit baseline: Mathlib master on 2026-08-24. Update together with `lean-toolchain`.
  require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git" @ "dc84fcbe9e049439c1c36d6db290cc0565f77788"

@[default_target]
lean_lib «EndKan» where
  roots := #[`EndKan, `EndKan.TestFixtures]

lean_lib «EndKan.Automation» where
  roots := #[`EndKan.Automation]

lean_lib «EndKan.Experimental» where
  roots := #[`EndKan.Experimental]

lean_lib «EndKan.ProductionBenchmarks» where
  roots := #[`EndKan.ProductionBenchmarks]

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

lean_lib Scratch where
  roots := #[`Scratch.SliceIsoMin, `Scratch.MathlibEndBetaExamples, `Scratch.MathlibCoendBetaExamples,
    `Scratch.MathlibFubiniExamples, `Scratch.MathlibKanBcExamples]
