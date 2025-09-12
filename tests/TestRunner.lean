import EndKan.TestInfrastructure.TestFramework
import EndKan.TestConfig
import EndKan.UnitTests.CoreFunctions
import EndKan.IntegrationTests.TacticInteractions
import EndKan.EndToEndTests.CompleteWorkflows
import EndKan.PerformanceTests.RegressionTests

namespace EndKan.TestRunner

open TestInfrastructure.TestFramework
open TestConfig

/-- Main test runner -/
def main (args : List String) : IO Unit := do
  -- Parse command line arguments
  let configName := args.head?.getD "dev"
  let testTypes := args.drop 1

  -- Get test configuration
  let config ← if configName = "env" then
    fromEnvironment
  else
    pure (getTestConfig configName)

  -- Validate configuration
  let validationErrors := validateTestConfig config
  if not validationErrors.isEmpty then
    IO.println s!"Configuration validation errors: {validationErrors.join \", \"}"
    return

  -- Print configuration summary
  if config.verbose then
    IO.println (summarizeTestConfig config)

  -- Convert to TestRunnerConfig
  let runnerConfig := toTestRunnerConfig config

  -- Create test suites
  let testSuites := createTestSuites config testTypes

  -- Run tests
  let startTime ← IO.monoMsNow
  let results ← runTestSuites testSuites runnerConfig
  let endTime ← IO.monoMsNow

  -- Generate reports
  let totalTime := endTime - startTime
  let report ← generateTestReport results
  IO.println report

  -- Check if tests passed
  let allPassed := validateTestResults results
  if allPassed then
    IO.println "All tests passed!"
    IO.Process.exit 0
  else
    IO.println "Some tests failed!"
    IO.Process.exit 1

/-- Create test suites based on configuration -/
def createTestSuites (config : TestConfig) (testTypes : List String) : List TestSuite :=
  let requestedTypes := if testTypes.isEmpty then config.testTypes else testTypes
  let allSuites : List TestSuite := [
    createTestSuite "Unit Tests" (UnitTests.CoreFunctions.allCoreFunctionTests.tests) (some setupUnitTests) (some teardownUnitTests)
    createTestSuite "Integration Tests" (IntegrationTests.TacticInteractions.allTacticInteractionTests.tests) (some setupIntegrationTests) (some teardownIntegrationTests)
    createTestSuite "End-to-End Tests" (EndToEndTests.CompleteWorkflows.allCompleteWorkflowTests.tests) (some setupE2ETests) (some teardownE2ETests)
    createTestSuite "Performance Tests" (PerformanceTests.RegressionTests.allPerformanceRegressionTests.tests) (some setupPerformanceTests) (some teardownPerformanceTests)
  ]

  allSuites.filter (fun suite =>
    requestedTypes.any (fun testType => suite.name.contains testType)
  )

/-- Setup functions for different test types -/
def setupUnitTests : IO Unit := do
  IO.println "Setting up unit tests..."
  -- Add any unit test setup here

def teardownUnitTests : IO Unit := do
  IO.println "Tearing down unit tests..."
  -- Add any unit test teardown here

def setupIntegrationTests : IO Unit := do
  IO.println "Setting up integration tests..."
  -- Add any integration test setup here

def teardownIntegrationTests : IO Unit := do
  IO.println "Tearing down integration tests..."
  -- Add any integration test teardown here

def setupE2ETests : IO Unit := do
  IO.println "Setting up end-to-end tests..."
  -- Add any E2E test setup here

def teardownE2ETests : IO Unit := do
  IO.println "Tearing down end-to-end tests..."
  -- Add any E2E test teardown here

def setupPerformanceTests : IO Unit := do
  IO.println "Setting up performance tests..."
  -- Add any performance test setup here

def teardownPerformanceTests : IO Unit := do
  IO.println "Tearing down performance tests..."
  -- Add any performance test teardown here

/-- Run specific test type -/
def runTestType (testType : String) (config : TestConfig) : IO (List TestResult) := do
  let testSuites := createTestSuites config [testType]
  let runnerConfig := toTestRunnerConfig config
  runTestSuites testSuites runnerConfig

/-- Run all tests -/
def runAllTests (config : TestConfig) : IO (List TestResult) := do
  let testSuites := createTestSuites config []
  let runnerConfig := toTestRunnerConfig config
  runTestSuites testSuites runnerConfig

/-- Run tests with custom configuration -/
def runTestsWithConfig (config : TestConfig) (testTypes : List String) : IO (List TestResult) := do
  let testSuites := createTestSuites config testTypes
  let runnerConfig := toTestRunnerConfig config
  runTestSuites testSuites runnerConfig

/-- Run tests in parallel -/
def runTestsParallel (config : TestConfig) (testTypes : List String) : IO (List TestResult) := do
  let testSuites := createTestSuites config testTypes
  let runnerConfig := { (toTestRunnerConfig config) with parallel := true }
  runTestSuites testSuites runnerConfig

/-- Run tests sequentially -/
def runTestsSequential (config : TestConfig) (testTypes : List String) : IO (List TestResult) := do
  let testSuites := createTestSuites config testTypes
  let runnerConfig := { (toTestRunnerConfig config) with parallel := false }
  runTestSuites testSuites runnerConfig

/-- Run tests with retry -/
def runTestsWithRetry (config : TestConfig) (testTypes : List String) : IO (List TestResult) := do
  let testSuites := createTestSuites config testTypes
  let runnerConfig := toTestRunnerConfig config
  let mut results : List TestResult := []

  for i in [0:config.retryCount] do
    if i > 0 then
      IO.println s!"Retry attempt {i + 1}/{config.retryCount}"
      IO.sleep config.retryDelay

    let attemptResults ← runTestSuites testSuites runnerConfig
    results := attemptResults

    if validateTestResults attemptResults then
      break

  return results

/-- Run tests with coverage -/
def runTestsWithCoverage (config : TestConfig) (testTypes : List String) : IO (List TestResult × String) := do
  let testSuites := createTestSuites config testTypes
  let runnerConfig := toTestRunnerConfig config
  let results ← runTestSuites testSuites runnerConfig

  let coverage ← analyzeTestCoverage testSuites
  return (results, coverage)

/-- Run tests with performance analysis -/
def runTestsWithPerformance (config : TestConfig) (testTypes : List String) : IO (List TestResult × String) := do
  let testSuites := createTestSuites config testTypes
  let runnerConfig := toTestRunnerConfig config
  let results ← runTestSuites testSuites runnerConfig

  let statistics ← generateTestStatistics results
  return (results, statistics)

/-- Run tests with regression detection -/
def runTestsWithRegression (config : TestConfig) (testTypes : List String) (baselineResults : List TestResult) : IO (List TestResult × List (String × Float)) := do
  let testSuites := createTestSuites config testTypes
  let runnerConfig := toTestRunnerConfig config
  let results ← runTestSuites testSuites runnerConfig

  let regressions ← detectPerformanceRegression results baselineResults
  return (results, regressions)

/-- Export test results -/
def exportTestResults (results : List TestResult) (formats : List String) : IO Unit := do
  for format in formats do
    match format with
    | "json" =>
      let json ← exportTestResultsToJson results
      IO.FS.writeFile "test-results.json" json
      IO.println "Exported test results to test-results.json"
    | "xml" =>
      let xml ← exportTestResultsToXml results
      IO.FS.writeFile "test-results.xml" xml
      IO.println "Exported test results to test-results.xml"
    | "csv" =>
      let csv ← exportTestResultsToCsv results
      IO.FS.writeFile "test-results.csv" csv
      IO.println "Exported test results to test-results.csv"
    | _ =>
      IO.println s!"Unknown output format: {format}"

/-- Print help message -/
def printHelp : IO Unit := do
  IO.println "EndKan Test Runner"
  IO.println "=================="
  IO.println ""
  IO.println "Usage: lake test [CONFIG] [TEST_TYPES...]"
  IO.println ""
  IO.println "Configurations:"
  IO.println "  dev       - Development configuration (default)"
  IO.println "  ci        - CI configuration"
  IO.println "  prod      - Production configuration"
  IO.println "  perf      - Performance configuration"
  IO.println "  security  - Security configuration"
  IO.println "  quality   - Quality configuration"
  IO.println "  doc       - Documentation configuration"
  IO.println "  env       - Configuration from environment variables"
  IO.println ""
  IO.println "Test Types:"
  IO.println "  unit      - Unit tests"
  IO.println "  integration - Integration tests"
  IO.println "  e2e       - End-to-end tests"
  IO.println "  performance - Performance tests"
  IO.println "  security  - Security tests"
  IO.println "  quality   - Quality tests"
  IO.println "  documentation - Documentation tests"
  IO.println ""
  IO.println "Examples:"
  IO.println "  lake test dev unit integration"
  IO.println "  lake test ci performance"
  IO.println "  lake test prod all"
  IO.println "  lake test env unit"

/-- Print version information -/
def printVersion : IO Unit := do
  IO.println "EndKan Test Runner v1.0.0"
  IO.println "Built with Lean 4"

/-- Print configuration information -/
def printConfig (configName : String) : IO Unit := do
  let config := getTestConfig configName
  IO.println (summarizeTestConfig config)

/-- Print available configurations -/
def printConfigs : IO Unit := do
  IO.println "Available test configurations:"
  for (name, _) in testConfigPresets do
    IO.println s!"  {name}"

/-- Print test statistics -/
def printStatistics (results : List TestResult) : IO Unit := do
  let statistics ← generateTestStatistics results
  IO.println statistics

/-- Print test coverage -/
def printCoverage (testSuites : List TestSuite) : IO Unit := do
  let coverage ← analyzeTestCoverage testSuites
  IO.println coverage

/-- Print performance regression -/
def printPerformanceRegression (currentResults : List TestResult) (baselineResults : List TestResult) : IO Unit := do
  let regressions ← detectPerformanceRegression currentResults baselineResults
  if regressions.isEmpty then
    IO.println "No performance regressions detected"
  else
    IO.println "Performance regressions detected:"
    for (name, ratio) in regressions do
      IO.println s!"  {name}: {ratio.toFloat}x slower"

/-- Print test comparison -/
def printTestComparison (results1 : List TestResult) (results2 : List TestResult) : IO Unit := do
  let comparison ← compareTestResults results1 results2
  IO.println comparison

/-- Print configuration comparison -/
def printConfigComparison (config1 : TestConfig) (config2 : TestConfig) : IO Unit := do
  let comparison ← compareTestConfigs config1 config2
  IO.println comparison

end EndKan.TestRunner
