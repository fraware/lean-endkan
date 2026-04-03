import EndKan.TestInfrastructure.TestFramework

namespace EndKan.TestConfig

open TestInfrastructure.TestFramework

/-- Test configuration for different environments -/
structure TestConfig where
  name : String
  timeout : Nat
  maxMemory : Nat
  verbose : Bool
  parallel : Bool
  maxParallelTests : Nat
  retryCount : Nat
  retryDelay : Nat
  testTypes : List String
  outputFormats : List String
  coverageThreshold : Float
  performanceThreshold : Float

/-- Development test configuration -/
def devTestConfig : TestConfig :=
  { name := "Development"
    timeout := 10000
    maxMemory := 50 * 1024 * 1024
    verbose := true
    parallel := true
    maxParallelTests := 4
    retryCount := 2
    retryDelay := 500
    testTypes := ["unit", "integration"]
    outputFormats := ["json", "console"]
    coverageThreshold := 80.0
    performanceThreshold := 1.2 }

/-- CI test configuration -/
def ciTestConfig : TestConfig :=
  { name := "CI"
    timeout := 30000
    maxMemory := 100 * 1024 * 1024
    verbose := true
    parallel := true
    maxParallelTests := 8
    retryCount := 3
    retryDelay := 1000
    testTypes := ["unit", "integration", "e2e", "performance"]
    outputFormats := ["json", "xml", "csv"]
    coverageThreshold := 90.0
    performanceThreshold := 1.1 }

/-- Production test configuration -/
def prodTestConfig : TestConfig :=
  { name := "Production"
    timeout := 60000
    maxMemory := 500 * 1024 * 1024
    verbose := false
    parallel := true
    maxParallelTests := 16
    retryCount := 5
    retryDelay := 2000
    testTypes := ["unit", "integration", "e2e", "performance", "security", "quality"]
    outputFormats := ["json", "xml", "csv", "html"]
    coverageThreshold := 95.0
    performanceThreshold := 1.05 }

/-- Performance test configuration -/
def perfTestConfig : TestConfig :=
  { name := "Performance"
    timeout := 120000
    maxMemory := 1000 * 1024 * 1024
    verbose := true
    parallel := false
    maxParallelTests := 1
    retryCount := 1
    retryDelay := 0
    testTypes := ["performance"]
    outputFormats := ["json", "xml"]
    coverageThreshold := 0.0
    performanceThreshold := 1.0 }

/-- Security test configuration -/
def securityTestConfig : TestConfig :=
  { name := "Security"
    timeout := 60000
    maxMemory := 200 * 1024 * 1024
    verbose := true
    parallel := false
    maxParallelTests := 1
    retryCount := 1
    retryDelay := 0
    testTypes := ["security"]
    outputFormats := ["json", "xml"]
    coverageThreshold := 0.0
    performanceThreshold := 1.0 }

/-- Quality test configuration -/
def qualityTestConfig : TestConfig :=
  { name := "Quality"
    timeout := 30000
    maxMemory := 100 * 1024 * 1024
    verbose := true
    parallel := false
    maxParallelTests := 1
    retryCount := 1
    retryDelay := 0
    testTypes := ["quality"]
    outputFormats := ["json", "xml"]
    coverageThreshold := 0.0
    performanceThreshold := 1.0 }

/-- Documentation test configuration -/
def docTestConfig : TestConfig :=
  { name := "Documentation"
    timeout := 60000
    maxMemory := 200 * 1024 * 1024
    verbose := true
    parallel := false
    maxParallelTests := 1
    retryCount := 1
    retryDelay := 0
    testTypes := ["documentation"]
    outputFormats := ["html", "pdf"]
    coverageThreshold := 0.0
    performanceThreshold := 1.0 }

/-- Get test configuration by name -/
def getTestConfig (name : String) : TestConfig :=
  match name with
  | "dev" => devTestConfig
  | "ci" => ciTestConfig
  | "prod" => prodTestConfig
  | "perf" => perfTestConfig
  | "security" => securityTestConfig
  | "quality" => qualityTestConfig
  | "doc" => docTestConfig
  | _ => devTestConfig

/-- Convert TestConfig to TestRunnerConfig -/
def toTestRunnerConfig (config : TestConfig) : TestRunnerConfig :=
  { timeout := config.timeout
    maxMemory := config.maxMemory
    verbose := config.verbose
    parallel := config.parallel
    maxParallelTests := config.maxParallelTests
    retryCount := config.retryCount
    retryDelay := config.retryDelay }

/-- Test configuration validation -/
def validateTestConfig (config : TestConfig) : List String :=
  let errors : List String := []
  let errors := if config.timeout ≤ 0 then "Timeout must be positive" :: errors else errors
  let errors := if config.maxMemory ≤ 0 then "Max memory must be positive" :: errors else errors
  let errors := if config.maxParallelTests ≤ 0 then "Max parallel tests must be positive" :: errors else errors
  let errors := if config.retryCount < 0 then "Retry count must be non-negative" :: errors else errors
  let errors := if config.retryDelay < 0 then "Retry delay must be non-negative" :: errors else errors
  let errors := if config.testTypes.isEmpty then "At least one test type must be specified" :: errors else errors
  let errors := if config.outputFormats.isEmpty then "At least one output format must be specified" :: errors else errors
  let errors := if config.coverageThreshold < 0.0 || config.coverageThreshold > 100.0 then "Coverage threshold must be between 0 and 100" :: errors else errors
  let errors := if config.performanceThreshold ≤ 0.0 then "Performance threshold must be positive" :: errors else errors
  errors

/-- Test configuration from environment variables -/
def fromEnvironment : IO TestConfig := do
  let name ← IO.getEnv "TEST_CONFIG" |>.getD "dev"
  let timeout ← (IO.getEnv "TEST_TIMEOUT" |>.getD "10000").toNat!
  let maxMemory ← (IO.getEnv "TEST_MAX_MEMORY" |>.getD "52428800").toNat!
  let verbose ← (IO.getEnv "TEST_VERBOSE" |>.getD "true").toBool!
  let parallel ← (IO.getEnv "TEST_PARALLEL" |>.getD "true").toBool!
  let maxParallelTests ← (IO.getEnv "TEST_MAX_PARALLEL" |>.getD "4").toNat!
  let retryCount ← (IO.getEnv "TEST_RETRY_COUNT" |>.getD "2").toNat!
  let retryDelay ← (IO.getEnv "TEST_RETRY_DELAY" |>.getD "500").toNat!
  let testTypes ← (IO.getEnv "TEST_TYPES" |>.getD "unit,integration").splitOn ","
  let outputFormats ← (IO.getEnv "TEST_OUTPUT_FORMATS" |>.getD "json,console").splitOn ","
  let coverageThreshold ← (IO.getEnv "TEST_COVERAGE_THRESHOLD" |>.getD "80.0").toFloat!
  let performanceThreshold ← (IO.getEnv "TEST_PERFORMANCE_THRESHOLD" |>.getD "1.2").toFloat!

  return {
    name
    timeout
    maxMemory
    verbose
    parallel
    maxParallelTests
    retryCount
    retryDelay
    testTypes
    outputFormats
    coverageThreshold
    performanceThreshold
  }

/-- Test configuration presets -/
def testConfigPresets : List (String × TestConfig) :=
  [("dev", devTestConfig)
   ("ci", ciTestConfig)
   ("prod", prodTestConfig)
   ("perf", perfTestConfig)
   ("security", securityTestConfig)
   ("quality", qualityTestConfig)
   ("doc", docTestConfig)]

/-- List available test configurations -/
def listTestConfigs : List String :=
  testConfigPresets.map (·.1)

/-- Get test configuration by preset name -/
def getTestConfigByPreset (preset : String) : Option TestConfig :=
  testConfigPresets.find? (·.1 = preset) |>.map (·.2)

/-- Test configuration comparison -/
def compareTestConfigs (config1 : TestConfig) (config2 : TestConfig) : String :=
  let differences : List String := []
  let differences := if config1.timeout ≠ config2.timeout then s!"Timeout: {config1.timeout} vs {config2.timeout}" :: differences else differences
  let differences := if config1.maxMemory ≠ config2.maxMemory then s!"Max Memory: {config1.maxMemory} vs {config2.maxMemory}" :: differences else differences
  let differences := if config1.verbose ≠ config2.verbose then s!"Verbose: {config1.verbose} vs {config2.verbose}" :: differences else differences
  let differences := if config1.parallel ≠ config2.parallel then s!"Parallel: {config1.parallel} vs {config2.parallel}" :: differences else differences
  let differences := if config1.maxParallelTests ≠ config2.maxParallelTests then s!"Max Parallel Tests: {config1.maxParallelTests} vs {config2.maxParallelTests}" :: differences else differences
  let differences := if config1.retryCount ≠ config2.retryCount then s!"Retry Count: {config1.retryCount} vs {config2.retryCount}" :: differences else differences
  let differences := if config1.retryDelay ≠ config2.retryDelay then s!"Retry Delay: {config1.retryDelay} vs {config2.retryDelay}" :: differences else differences
  let differences := if config1.testTypes ≠ config2.testTypes then s!"Test Types: {config1.testTypes} vs {config2.testTypes}" :: differences else differences
  let differences := if config1.outputFormats ≠ config2.outputFormats then s!"Output Formats: {config1.outputFormats} vs {config2.outputFormats}" :: differences else differences
  let differences := if config1.coverageThreshold ≠ config2.coverageThreshold then s!"Coverage Threshold: {config1.coverageThreshold} vs {config2.coverageThreshold}" :: differences else differences
  let differences := if config1.performanceThreshold ≠ config2.performanceThreshold then s!"Performance Threshold: {config1.performanceThreshold} vs {config2.performanceThreshold}" :: differences else differences

  if differences.isEmpty then
    "Configurations are identical"
  else
    s!"Configuration differences:\n{differences.join \"\n\"}"

/-- Test configuration summary -/
def summarizeTestConfig (config : TestConfig) : String :=
  s!"Test Configuration: {config.name}\n"
  ++ s!"==================\n"
  ++ s!"Timeout: {config.timeout}ms\n"
  ++ s!"Max Memory: {config.maxMemory} bytes\n"
  ++ s!"Verbose: {config.verbose}\n"
  ++ s!"Parallel: {config.parallel}\n"
  ++ s!"Max Parallel Tests: {config.maxParallelTests}\n"
  ++ s!"Retry Count: {config.retryCount}\n"
  ++ s!"Retry Delay: {config.retryDelay}ms\n"
  ++ s!"Test Types: {config.testTypes.join \", \"}\n"
  ++ s!"Output Formats: {config.outputFormats.join \", \"}\n"
  ++ s!"Coverage Threshold: {config.coverageThreshold}%\n"
  ++ s!"Performance Threshold: {config.performanceThreshold}x\n"

end EndKan.TestConfig
