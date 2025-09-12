import Lake
open Lake DSL

package «lean-endkan» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «EndKan» where
  -- add library configuration options here

-- Production benchmarks
lean_lib «EndKan.ProductionBenchmarks» where
  -- Production benchmarking library

-- Telemetry and monitoring
lean_lib «EndKan.Telemetry» where
  -- Telemetry and monitoring library

-- Optimization
lean_lib «EndKan.Optimization» where
  -- Algorithm optimization library

-- Configuration management
lean_lib «EndKan.Configuration» where
  -- Configuration management library

-- Production monitoring
lean_lib «EndKan.Monitoring» where
  -- Production monitoring library
