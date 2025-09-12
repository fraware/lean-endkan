import Lake
open Lake DSL

package "EndKan" where
  -- Add package configuration here

@[default_target]
lean_lib "EndKan" where
  -- Add library configuration here

@[default_target]
lean_exe "test-runner" where
  root := `TestRunner
  supportInterpreter := true

lean_exe "unit-tests" where
  root := `UnitTests.CoreFunctions
  supportInterpreter := true

lean_exe "integration-tests" where
  root := `IntegrationTests.TacticInteractions
  supportInterpreter := true

lean_exe "e2e-tests" where
  root := `EndToEndTests.CompleteWorkflows
  supportInterpreter := true

lean_exe "performance-tests" where
  root := `PerformanceTests.RegressionTests
  supportInterpreter := true

lean_exe "test-framework" where
  root := `TestInfrastructure.TestFramework
  supportInterpreter := true

lean_exe "test-config" where
  root := `TestConfig
  supportInterpreter := true

-- Test targets
target "test" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["dev", "unit", "integration", "e2e", "performance"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "30000"),
      ("LEAN_TEST_MEMORY_LIMIT", "100000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "true"),
      ("LEAN_TEST_MAX_PARALLEL", "4")
    ]
  }.run

target "test-unit" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["dev", "unit"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "10000"),
      ("LEAN_TEST_MEMORY_LIMIT", "50000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "true"),
      ("LEAN_TEST_MAX_PARALLEL", "4")
    ]
  }.run

target "test-integration" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["dev", "integration"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "20000"),
      ("LEAN_TEST_MEMORY_LIMIT", "75000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "true"),
      ("LEAN_TEST_MAX_PARALLEL", "4")
    ]
  }.run

target "test-e2e" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["dev", "e2e"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "30000"),
      ("LEAN_TEST_MEMORY_LIMIT", "100000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "false"),
      ("LEAN_TEST_MAX_PARALLEL", "1")
    ]
  }.run

target "test-performance" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["perf", "performance"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "120000"),
      ("LEAN_TEST_MEMORY_LIMIT", "1000000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "false"),
      ("LEAN_TEST_MAX_PARALLEL", "1")
    ]
  }.run

target "test-all" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["ci", "unit", "integration", "e2e", "performance"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "60000"),
      ("LEAN_TEST_MEMORY_LIMIT", "500000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "true"),
      ("LEAN_TEST_MAX_PARALLEL", "8")
    ]
  }.run

-- CI targets
target "ci-test" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["ci", "unit", "integration", "e2e", "performance"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "30000"),
      ("LEAN_TEST_MEMORY_LIMIT", "100000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "true"),
      ("LEAN_TEST_MAX_PARALLEL", "8")
    ]
  }.run

target "ci-performance" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["perf", "performance"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "120000"),
      ("LEAN_TEST_MEMORY_LIMIT", "1000000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "false"),
      ("LEAN_TEST_MAX_PARALLEL", "1")
    ]
  }.run

-- Production targets
target "prod-test" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["prod", "unit", "integration", "e2e", "performance", "security", "quality"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "60000"),
      ("LEAN_TEST_MEMORY_LIMIT", "500000000"),
      ("LEAN_TEST_VERBOSE", "false"),
      ("LEAN_TEST_PARALLEL", "true"),
      ("LEAN_TEST_MAX_PARALLEL", "16")
    ]
  }.run

-- Development targets
target "dev-test" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["dev", "unit", "integration"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "10000"),
      ("LEAN_TEST_MEMORY_LIMIT", "50000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "true"),
      ("LEAN_TEST_MAX_PARALLEL", "4")
    ]
  }.run

-- Quick test target
target "quick-test" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["dev", "unit"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "5000"),
      ("LEAN_TEST_MEMORY_LIMIT", "10000000"),
      ("LEAN_TEST_VERBOSE", "false"),
      ("LEAN_TEST_PARALLEL", "false"),
      ("LEAN_TEST_MAX_PARALLEL", "1")
    ]
  }.run

-- Test report targets
target "test-report" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["ci", "unit", "integration", "e2e", "performance"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "30000"),
      ("LEAN_TEST_MEMORY_LIMIT", "100000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "true"),
      ("LEAN_TEST_MAX_PARALLEL", "8"),
      ("LEAN_TEST_OUTPUT_FORMATS", "json,xml,csv")
    ]
  }.run

-- Coverage target
target "test-coverage" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["ci", "unit", "integration", "e2e", "performance"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "30000"),
      ("LEAN_TEST_MEMORY_LIMIT", "100000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "true"),
      ("LEAN_TEST_MAX_PARALLEL", "8"),
      ("LEAN_TEST_COVERAGE", "true")
    ]
  }.run

-- Performance regression target
target "test-regression" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["perf", "performance"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "120000"),
      ("LEAN_TEST_MEMORY_LIMIT", "1000000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "false"),
      ("LEAN_TEST_MAX_PARALLEL", "1"),
      ("LEAN_TEST_REGRESSION", "true")
    ]
  }.run

-- Security test target
target "test-security" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["security", "security"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "60000"),
      ("LEAN_TEST_MEMORY_LIMIT", "200000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "false"),
      ("LEAN_TEST_MAX_PARALLEL", "1")
    ]
  }.run

-- Quality test target
target "test-quality" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["quality", "quality"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "30000"),
      ("LEAN_TEST_MEMORY_LIMIT", "100000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "false"),
      ("LEAN_TEST_MAX_PARALLEL", "1")
    ]
  }.run

-- Documentation test target
target "test-docs" : Unit → IO PUnit := do
  let testRunner ← getLeanExe "test-runner"
  testRunner.proc {
    args := #["doc", "documentation"]
    env := #[
      ("LEAN_TEST_TIMEOUT", "60000"),
      ("LEAN_TEST_MEMORY_LIMIT", "200000000"),
      ("LEAN_TEST_VERBOSE", "true"),
      ("LEAN_TEST_PARALLEL", "false"),
      ("LEAN_TEST_MAX_PARALLEL", "1")
    ]
  }.run
