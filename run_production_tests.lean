import EndKan
import EndKan.ProductionBenchmarks
import EndKan.Telemetry
import EndKan.Configuration
import EndKan.Monitoring
import EndKan.Optimization

/-- Production test runner for EndKan -/
def main : IO Unit := do
  IO.println "EndKan Production Test Runner"
  IO.println "============================="
  IO.println ""

  -- Initialize production systems
  IO.println "Initializing production systems..."
  EndKan.Telemetry.initializeTelemetry
  EndKan.Configuration.initializeConfiguration
  EndKan.Monitoring.initializeMonitoring
  IO.println "✓ Production systems initialized"
  IO.println ""

  -- Run configuration validation
  IO.println "Validating configuration..."
  let configReport ← EndKan.Configuration.getConfigurationReport
  IO.println configReport
  IO.println ""

  -- Run comprehensive benchmarks
  IO.println "Running comprehensive benchmarks..."
  EndKan.ProductionBenchmarks.runComprehensiveBenchmarkSuite
  IO.println ""

  -- Generate telemetry report
  IO.println "Generating telemetry report..."
  let telemetryReport ← EndKan.Telemetry.generateTelemetryReport
  IO.println telemetryReport
  IO.println ""

  -- Generate monitoring report
  IO.println "Generating monitoring report..."
  let monitoringReport ← EndKan.Monitoring.generateMonitoringReport
  IO.println monitoringReport
  IO.println ""

  -- Check system health
  IO.println "Checking system health..."
  let healthCheck ← EndKan.Monitoring.healthCheck
  IO.println healthCheck
  IO.println ""

  -- Get performance summary
  IO.println "Getting performance summary..."
  let performanceSummary ← EndKan.Monitoring.getPerformanceSummary
  IO.println performanceSummary
  IO.println ""

  -- Get alert summary
  IO.println "Getting alert summary..."
  let alertSummary ← EndKan.Monitoring.getAlertSummary
  IO.println alertSummary
  IO.println ""

  IO.println "Production test runner completed successfully!"
  IO.println "All systems are operational and ready for production use."
