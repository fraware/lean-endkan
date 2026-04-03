import EndKan
import EndKan.ProductionBenchmarks
import EndKan.Telemetry
import EndKan.Configuration
import EndKan.Monitoring
import EndKan.Optimization

/-- Demo script that walks through config and monitoring helpers. -/
def main : IO Unit := do
  IO.println "EndKan demo deployment walkthrough"
  IO.println "=================================="
  IO.println ""

  IO.println "Running pre-checks..."

  EndKan.Telemetry.initializeTelemetry
  EndKan.Configuration.initializeConfiguration
  EndKan.Monitoring.initializeMonitoring

  let configValidation ← EndKan.Configuration.validateConfiguration
  match configValidation with
  | .valid => IO.println "✓ Configuration validation passed"
  | .invalid msg => do
      IO.println s!"✗ Configuration validation failed: {msg}"
      return

  let healthCheck ← EndKan.Monitoring.healthCheck
  IO.println s!"✓ System health check: {healthCheck}"

  IO.println "Running performance benchmarks..."
  EndKan.ProductionBenchmarks.runComprehensiveBenchmarkSuite

  IO.println "Performance regression gate: not implemented in this demo."

  IO.println "Switching configuration to the demo 'production' profile..."
  EndKan.Configuration.switchEnvironment .production
  IO.println "✓ Switched to demo production profile"

  IO.println "Verifying deployment..."
  let postDeployHealth ← EndKan.Monitoring.healthCheck
  IO.println s!"✓ Post-deployment health check: {postDeployHealth}"

  IO.println "Generating deployment report..."
  let monitoringReport ← EndKan.Monitoring.generateMonitoringReport
  IO.println monitoringReport

  IO.println ""
  IO.println "Demo deployment walkthrough finished."
  IO.println "Nothing was deployed to a real environment."
  IO.println ""
  IO.println "If you ship something real, add your own checks, hosting, and monitoring."
