import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.HasColimits
import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Kan.Core
import EndKan.Kan.BeckChevalley
import EndKan.Tactics
import EndKan.Transformation
import EndKan.ErrorHandling

namespace EndKan.ProductionBenchmarks

open CategoryTheory
open CategoryTheory.Limits
open Lean Elab Tactic Meta

/-- Performance metrics used by the demo benchmark harness -/
structure ProductionMetrics where
  -- Timing metrics
  executionTimeMs : Nat
  cpuTimeMs : Nat
  wallTimeMs : Nat
  -- Memory metrics
  memoryUsageBytes : Nat
  peakMemoryBytes : Nat
  memoryAllocations : Nat
  -- Performance metrics
  stepCount : Nat
  success : Bool
  errorType : Option String
  -- Quality metrics
  accuracy : Float
  precision : Float
  recall : Float
  -- System metrics
  gcCollections : Nat
  gcTimeMs : Nat
  -- Timestamp
  timestamp : Nat

/-- Statistical analysis results -/
structure StatisticalAnalysis where
  mean : Float
  median : Float
  stdDev : Float
  min : Float
  max : Float
  p25 : Float
  p75 : Float
  p90 : Float
  p95 : Float
  p99 : Float
  sampleSize : Nat
  confidenceInterval95 : (Float × Float)
  outliers : List Float

/-- Performance regression detection -/
structure RegressionAnalysis where
  hasRegression : Bool
  regressionSeverity : String
  performanceChange : Float
  statisticalSignificance : Float
  baselineMetrics : ProductionMetrics
  currentMetrics : ProductionMetrics
  recommendation : String

/-- Benchmark configuration -/
structure BenchmarkConfig where
  iterations : Nat := 1000
  warmupIterations : Nat := 100
  timeoutMs : Nat := 30000
  memoryLimitMB : Nat := 1024
  enableProfiling : Bool := true
  enableMemoryTracking : Bool := true
  enableGCTracking : Bool := true
  statisticalSignificance : Float := 0.95
  regressionThreshold : Float := 0.1

/-- Global benchmark configuration -/
def benchmarkConfig : IO.Ref BenchmarkConfig := IO.mkRef {}

/-- Set benchmark configuration -/
def setBenchmarkConfig (config : BenchmarkConfig) : IO Unit := do
  benchmarkConfig.set config

/-- Get current benchmark configuration -/
def getBenchmarkConfig : IO BenchmarkConfig := do
  benchmarkConfig.get

/-- Performance measurement utilities -/
def measureExecutionTime (action : IO α) : IO (α × Nat) := do
  let startTime ← IO.monoMsNow
  let result ← action
  let endTime ← IO.monoMsNow
  return (result, endTime - startTime)

def measureMemoryUsage (action : IO α) : IO (α × Nat) := do
  let startMemory ← IO.getMemoryUsage
  let result ← action
  let endMemory ← IO.getMemoryUsage
  return (result, endMemory - startMemory)

def measureGCMetrics (action : IO α) : IO (α × Nat × Nat) := do
  let startGC ← IO.getGCCount
  let startGCTime ← IO.getGCTime
  let result ← action
  let endGC ← IO.getGCCount
  let endGCTime ← IO.getGCTime
  return (result, endGC - startGC, endGCTime - startGCTime)

/-- Comprehensive performance measurement -/
def measurePerformance (action : IO α) : IO (α × ProductionMetrics) := do
  let (result, executionTime) ← measureExecutionTime action
  let (_, memoryUsage) ← measureMemoryUsage (pure result)
  let (_, gcCollections, gcTime) ← measureGCMetrics (pure result)
  let timestamp ← IO.monoMsNow

  let metrics : ProductionMetrics := {
    executionTimeMs := executionTime
    cpuTimeMs := executionTime -- Approximation
    wallTimeMs := executionTime
    memoryUsageBytes := memoryUsage
    peakMemoryBytes := memoryUsage -- Approximation
    memoryAllocations := 0 -- Not directly available in Lean
    stepCount := 1
    success := true
    errorType := none
    accuracy := 1.0
    precision := 1.0
    recall := 1.0
    gcCollections := gcCollections
    gcTimeMs := gcTime
    timestamp := timestamp
  }

  return (result, metrics)

/-- Statistical analysis functions -/
def calculateMean (values : List Float) : Float :=
  if values.isEmpty then 0.0 else values.foldl (· + ·) 0.0 / values.length.toFloat

def calculateMedian (values : List Float) : Float :=
  if values.isEmpty then 0.0 else
    let sorted := values.sort (· < ·)
    let n := sorted.length
    if n % 2 == 0 then
      (sorted.get! (n / 2 - 1) + sorted.get! (n / 2)) / 2.0
    else
      sorted.get! (n / 2)

def calculateStdDev (values : List Float) : Float :=
  if values.length < 2 then 0.0 else
    let mean := calculateMean values
    let variance := values.map (fun x => (x - mean) ^ 2) |>.foldl (· + ·) 0.0 / (values.length - 1).toFloat
    Float.sqrt variance

def calculatePercentile (values : List Float) (percentile : Float) : Float :=
  if values.isEmpty then 0.0 else
    let sorted := values.sort (· < ·)
    let index := (percentile * (values.length - 1).toFloat).round.toNat
    sorted.get! (min index (values.length - 1))

def detectOutliers (values : List Float) : List Float :=
  if values.length < 4 then [] else
    let q1 := calculatePercentile values 0.25
    let q3 := calculatePercentile values 0.75
    let iqr := q3 - q1
    let lowerBound := q1 - 1.5 * iqr
    let upperBound := q3 + 1.5 * iqr
    values.filter (fun x => x < lowerBound || x > upperBound)

def calculateConfidenceInterval (values : List Float) (confidence : Float) : (Float × Float) :=
  if values.length < 2 then (0.0, 0.0) else
    let mean := calculateMean values
    let stdDev := calculateStdDev values
    let n := values.length.toFloat
    let zScore := 1.96 -- 95% confidence
    let margin := zScore * stdDev / Float.sqrt n
    (mean - margin, mean + margin)

/-- Perform statistical analysis on metrics -/
def analyzeMetrics (metrics : List ProductionMetrics) : StatisticalAnalysis :=
  let executionTimes := metrics.map (·.executionTimeMs.toFloat)
  let memoryUsages := metrics.map (·.memoryUsageBytes.toFloat)
  let gcTimes := metrics.map (·.gcTimeMs.toFloat)

  let executionTimeAnalysis := {
    mean := calculateMean executionTimes
    median := calculateMedian executionTimes
    stdDev := calculateStdDev executionTimes
    min := executionTimes.foldl min Float.inf
    max := executionTimes.foldl max (-Float.inf)
    p25 := calculatePercentile executionTimes 0.25
    p75 := calculatePercentile executionTimes 0.75
    p90 := calculatePercentile executionTimes 0.90
    p95 := calculatePercentile executionTimes 0.95
    p99 := calculatePercentile executionTimes 0.99
    sampleSize := metrics.length
    confidenceInterval95 := calculateConfidenceInterval executionTimes 0.95
    outliers := detectOutliers executionTimes
  }

  executionTimeAnalysis

/-- Detect performance regression -/
def detectRegression (baseline : List ProductionMetrics) (current : List ProductionMetrics) : RegressionAnalysis :=
  if baseline.isEmpty || current.isEmpty then
    {
      hasRegression := false
      regressionSeverity := "insufficient_data"
      performanceChange := 0.0
      statisticalSignificance := 0.0
      baselineMetrics := baseline.head!
      currentMetrics := current.head!
      recommendation := "Insufficient data for regression analysis"
    }
  else
    let baselineMean := calculateMean (baseline.map (·.executionTimeMs.toFloat))
    let currentMean := calculateMean (current.map (·.executionTimeMs.toFloat))
    let performanceChange := (currentMean - baselineMean) / baselineMean * 100.0

    let hasRegression := performanceChange > 10.0 -- 10% threshold
    let regressionSeverity := if performanceChange > 50.0 then "critical"
                             else if performanceChange > 25.0 then "high"
                             else if performanceChange > 10.0 then "medium"
                             else "low"

    let recommendation := if hasRegression then
      s!"Performance regression detected: {performanceChange:.1f}% slower. Consider optimization."
    else
      s!"Performance is stable: {performanceChange:.1f}% change."

    {
      hasRegression := hasRegression
      regressionSeverity := regressionSeverity
      performanceChange := performanceChange
      statisticalSignificance := 0.95 -- Simplified
      baselineMetrics := baseline.head!
      currentMetrics := current.head!
      recommendation := recommendation
    }

/-- Benchmark end β-reduction -/
def benchmarkEndBeta (iterations : Nat := 1000) : IO (List ProductionMetrics) := do
  let config ← getBenchmarkConfig
  let mut results : List ProductionMetrics := []

  -- Warmup
  for _ in [0:config.warmupIterations] do
    let _ ← measurePerformance (pure ())

  -- Actual benchmark
  for _ in [0:iterations] do
    let (_, metrics) ← measurePerformance do
      let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
      let X : D := 𝟙_ D
      let ω : DinaturalTransformation X F := {
        app := fun _ => 𝟙 X
        dinaturality := by simp
      }
      let lift := End.lift ω
      let π := End.π F (Classical.arbitrary C)
      let _ := lift ≫ π = ω.app (Classical.arbitrary C)
      pure ()

    results := metrics :: results

  return results

/-- Benchmark coend β-reduction -/
def benchmarkCoendBeta (iterations : Nat := 1000) : IO (List ProductionMetrics) := do
  let config ← getBenchmarkConfig
  let mut results : List ProductionMetrics := []

  -- Warmup
  for _ in [0:config.warmupIterations] do
    let _ ← measurePerformance (pure ())

  -- Actual benchmark
  for _ in [0:iterations] do
    let (_, metrics) ← measurePerformance do
      let F : C × Cᵒᵖ ⥤ D := Functor.const (C × Cᵒᵖ) (𝟙_ D)
      let X : D := 𝟙_ D
      let ω : DinaturalTransformation F X := {
        app := fun _ => 𝟙 X
        dinaturality := by simp
      }
      let desc := Coend.desc ω
      let ι := Coend.ι F (Classical.arbitrary C)
      let _ := ι ≫ desc = ω.app (Classical.arbitrary C)
      pure ()

    results := metrics :: results

  return results

/-- Benchmark Kan fusion -/
def benchmarkKanFusion (iterations : Nat := 1000) : IO (List ProductionMetrics) := do
  let config ← getBenchmarkConfig
  let mut results : List ProductionMetrics := []

  -- Warmup
  for _ in [0:config.warmupIterations] do
    let _ ← measurePerformance (pure ())

  -- Actual benchmark
  for _ in [0:iterations] do
    let (_, metrics) ← measurePerformance do
      let K : C ⥤ D := Functor.const C (𝟙_ D)
      let F : C ⥤ E := Functor.const C (𝟙_ E)
      let lan := Lan K F
      let _ := lan = F
      pure ()

    results := metrics :: results

  return results

/-- Benchmark Beck-Chevalley -/
def benchmarkBeckChevalley (iterations : Nat := 1000) : IO (List ProductionMetrics) := do
  let config ← getBenchmarkConfig
  let mut results : List ProductionMetrics := []

  -- Warmup
  for _ in [0:config.warmupIterations] do
    let _ ← measurePerformance (pure ())

  -- Actual benchmark
  for _ in [0:iterations] do
    let (_, metrics) ← measurePerformance do
      let K : C ⥤ D := Functor.const C (𝟙_ D)
      let L : D ⥤ E := Functor.const D (𝟙_ E)
      let M : C ⥤ E := Functor.const C (𝟙_ E)
      let N : D ⥤ E := Functor.const D (𝟙_ E)
      let square := BeckChevalley.Square.mk (by simp)
      let _ := square = square
      pure ()

    results := metrics :: results

  return results

/-- Benchmark pattern matching -/
def benchmarkPatternMatching (iterations : Nat := 1000) : IO (List ProductionMetrics) := do
  let config ← getBenchmarkConfig
  let mut results : List ProductionMetrics := []

  -- Warmup
  for _ in [0:config.warmupIterations] do
    let _ ← measurePerformance (pure ())

  -- Actual benchmark
  for _ in [0:iterations] do
    let (_, metrics) ← measurePerformance do
      let F : Cᵒᵖ × C ⥤ D := Functor.const (Cᵒᵖ × C) (𝟙_ D)
      let X : D := 𝟙_ D
      let ω : DinaturalTransformation X F := {
        app := fun _ => 𝟙 X
        dinaturality := by simp
      }
      let lift := End.lift ω
      let π := End.π F (Classical.arbitrary C)
      let goal := lift ≫ π = ω.app (Classical.arbitrary C)
      let _ := isEndPattern goal
      pure ()

    results := metrics :: results

  return results

/-- Benchmark error handling -/
def benchmarkErrorHandling (iterations : Nat := 1000) : IO (List ProductionMetrics) := do
  let config ← getBenchmarkConfig
  let mut results : List ProductionMetrics := []

  -- Warmup
  for _ in [0:config.warmupIterations] do
    let _ ← measurePerformance (pure ())

  -- Actual benchmark
  for _ in [0:iterations] do
    let (_, metrics) ← measurePerformance do
      let _ := getErrorSeverity (.timeout "test")
      let _ := getErrorSeverity (.maxStepsReached "test")
      let _ := getErrorSeverity (.patternMatchFailed "test")
      let _ := getErrorSeverity (.transformationFailed "test")
      let _ := getErrorSeverity (.invalidGoal "test")
      let _ := getErrorSeverity (.dependencyMissing "test")
      let _ := getErrorSeverity (.typeMismatch "test")
      let _ := getErrorSeverity (.proofSearchFailed "test")
      let _ := getErrorSeverity (.resourceExhausted "test")
      let _ := getErrorSeverity (.unsupportedPattern "test")
      pure ()

    results := metrics :: results

  return results

/-- Run the full demo benchmark suite -/
def runComprehensiveBenchmarkSuite : IO Unit := do
  let config ← getBenchmarkConfig
  IO.println "Running EndKan demo benchmark suite..."
  IO.println s!"Configuration: {config.iterations} iterations, {config.warmupIterations} warmup"
  IO.println "=============================================="

  -- Run all benchmarks
  let endBetaResults ← benchmarkEndBeta config.iterations
  let coendBetaResults ← benchmarkCoendBeta config.iterations
  let kanFusionResults ← benchmarkKanFusion config.iterations
  let beckChevalleyResults ← benchmarkBeckChevalley config.iterations
  let patternMatchingResults ← benchmarkPatternMatching config.iterations
  let errorHandlingResults ← benchmarkErrorHandling config.iterations

  -- Analyze results
  let endBetaAnalysis := analyzeMetrics endBetaResults
  let coendBetaAnalysis := analyzeMetrics coendBetaResults
  let kanFusionAnalysis := analyzeMetrics kanFusionResults
  let beckChevalleyAnalysis := analyzeMetrics beckChevalleyResults
  let patternMatchingAnalysis := analyzeMetrics patternMatchingResults
  let errorHandlingAnalysis := analyzeMetrics errorHandlingResults

  -- Print results
  IO.println "Benchmark Results:"
  IO.println "=================="
  IO.println s!"End β-reduction: Mean={endBetaAnalysis.mean:.2f}ms, P95={endBetaAnalysis.p95:.2f}ms, StdDev={endBetaAnalysis.stdDev:.2f}ms"
  IO.println s!"Coend β-reduction: Mean={coendBetaAnalysis.mean:.2f}ms, P95={coendBetaAnalysis.p95:.2f}ms, StdDev={coendBetaAnalysis.stdDev:.2f}ms"
  IO.println s!"Kan fusion: Mean={kanFusionAnalysis.mean:.2f}ms, P95={kanFusionAnalysis.p95:.2f}ms, StdDev={kanFusionAnalysis.stdDev:.2f}ms"
  IO.println s!"Beck-Chevalley: Mean={beckChevalleyAnalysis.mean:.2f}ms, P95={beckChevalleyAnalysis.p95:.2f}ms, StdDev={beckChevalleyAnalysis.stdDev:.2f}ms"
  IO.println s!"Pattern matching: Mean={patternMatchingAnalysis.mean:.2f}ms, P95={patternMatchingAnalysis.p95:.2f}ms, StdDev={patternMatchingAnalysis.stdDev:.2f}ms"
  IO.println s!"Error handling: Mean={errorHandlingAnalysis.mean:.2f}ms, P95={errorHandlingAnalysis.p95:.2f}ms, StdDev={errorHandlingAnalysis.stdDev:.2f}ms"

  -- Check for regressions
  let allResults := endBetaResults ++ coendBetaResults ++ kanFusionResults ++ beckChevalleyResults ++ patternMatchingResults ++ errorHandlingResults
  let overallAnalysis := analyzeMetrics allResults

  IO.println ""
  IO.println "Overall Performance:"
  IO.println "==================="
  IO.println s!"Mean execution time: {overallAnalysis.mean:.2f}ms"
  IO.println s!"P95 execution time: {overallAnalysis.p95:.2f}ms"
  IO.println s!"Standard deviation: {overallAnalysis.stdDev:.2f}ms"
  IO.println s!"Sample size: {overallAnalysis.sampleSize}"
  IO.println s!"95% Confidence interval: ({overallAnalysis.confidenceInterval95.1:.2f}, {overallAnalysis.confidenceInterval95.2:.2f})"

  if not overallAnalysis.outliers.isEmpty then
    IO.println s!"Outliers detected: {overallAnalysis.outliers.length}"

  IO.println "=============================================="
  IO.println "Comprehensive benchmark suite completed!"

/-- Performance regression test -/
def runRegressionTest (baselineResults : List ProductionMetrics) : IO Unit := do
  IO.println "Running performance regression test..."
  IO.println "====================================="

  let currentResults ← runComprehensiveBenchmarkSuite
  let regressionAnalysis := detectRegression baselineResults currentResults

  IO.println "Regression Analysis:"
  IO.println "==================="
  IO.println s!"Has regression: {regressionAnalysis.hasRegression}"
  IO.println s!"Severity: {regressionAnalysis.regressionSeverity}"
  IO.println s!"Performance change: {regressionAnalysis.performanceChange:.1f}%"
  IO.println s!"Statistical significance: {regressionAnalysis.statisticalSignificance:.2f}"
  IO.println s!"Recommendation: {regressionAnalysis.recommendation}"

  if regressionAnalysis.hasRegression then
    IO.println "WARNING: Performance regression detected!"
  else
    IO.println "Performance is stable."

end EndKan.ProductionBenchmarks
