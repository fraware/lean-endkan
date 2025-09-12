import EndKan.End.Core
import EndKan.End.BetaEta
import EndKan.Coend.Core
import EndKan.Coend.BetaEta
import EndKan.Fubini
import EndKan.Kan.Core
import EndKan.Kan.BeckChevalley
import EndKan.Tactics
import EndKan.Attr
import EndKan.Telemetry
import EndKan.Optimization
import EndKan.Configuration
import EndKan.Monitoring

/-- EndKan: Production-Ready Automation for Category Theory in Lean 4

This library provides comprehensive automation for ends, coends, Kan extensions, and Beck-Chevalley
transformations with sophisticated pattern matching, transformation logic, and error handling.

## Main Features

### Advanced Tactics
- `end_beta` / `end_eta` — perform standard β/η for ends with pattern matching
- `coend_beta` / `coend_eta` — analogous transformations for coends with pattern matching
- `kan_fuse` — fuses Kan constructions via known universal properties
- `beck_chevalley!` — check/apply Beck–Chevalley with automatic pattern detection
- `endkan_smart` — automatically detects patterns and applies appropriate transformations
- `endkan_debug` — shows detected patterns and available strategies

### Enhanced Tactics with Error Handling
- `end_beta!` / `end_eta!` — enhanced versions with comprehensive error handling
- `coend_beta!` / `coend_eta!` — enhanced versions with comprehensive error handling
- `kan_fuse!` — enhanced version with comprehensive error handling
- `beck_chevalley!!` — enhanced version with comprehensive error handling

### Pattern Matching System
- Automatic goal analysis and pattern detection
- Support for ends, coends, Kan extensions, Beck-Chevalley, dinaturality, functor composition, natural transformations, and limits/colimits
- Intelligent strategy selection based on detected patterns

### Error Handling and Recovery
- Comprehensive error types and severity levels
- Timeout management and step counting
- Resource monitoring and error recovery
- Detailed error reporting and debugging

### Configuration Options
- `setTimeout ms` — sets the timeout in milliseconds
- `setTrace b` — enables or disables tracing
- `setMaxSteps n` — sets the maximum number of steps for tactics
- `setDebug b` — enables or disables debug mode
- `setAggressive b` — enables or disables aggressive transformations

### Production Features
- **Comprehensive Benchmarking**: Statistical analysis, performance regression detection, and automated performance testing
- **Telemetry & Monitoring**: Real-time metrics collection, performance dashboards, and alerting system
- **Algorithm Optimization**: Cached pattern matching, optimized data structures, and memory management
- **Configuration Management**: Environment-specific settings, validation, and secure configuration handling
- **Production Monitoring**: Health checks, performance thresholds, and automated alerting

## Quick Start

```lean
import EndKan

-- Use smart tactics that automatically detect patterns
example (F : Cᵒᵖ × C ⥤ D) (c : C) :
  End.lift (fun c => f c) h ≫ End.π F c = f c := by
  endkan_smart

-- Use enhanced tactics with error handling
example (K : C ⥤ D) (F : C ⥤ E) (hK : Full K) (hK' : Faithful K) :
  Lan K F ≅ F := by
  kan_fuse!

-- Use debug mode to see what's happening
example (S : BeckChevalley.Square K L M N) [BeckChevalley S] :
  M ⋙ Lan L (𝟙 E) ≅ Lan K (𝟙 D) ⋙ N := by
  endkan_debug
```

## Advanced Usage

### Pattern-Specific Tactics
```lean
-- End patterns
end_beta
end_eta

-- Coend patterns
coend_beta
coend_eta

-- Kan extension patterns
kan_fuse

-- Beck-Chevalley patterns
beck_chevalley!

-- Combined tactics
endkan_beta
endkan_eta
endkan_all
```

### Configuration and Debugging
```lean
-- Set configuration
setTimeout 5000
setTrace true
setDebug true
setAggressive true

-- Use tactics
endkan_smart
```

### Production Usage
```lean
-- Initialize production systems
EndKan.Telemetry.initializeTelemetry
EndKan.Configuration.initializeConfiguration
EndKan.Monitoring.initializeMonitoring

-- Run comprehensive benchmarks
EndKan.ProductionBenchmarks.runComprehensiveBenchmarkSuite

-- Generate monitoring reports
EndKan.Monitoring.generateMonitoringReport

-- Check system health
EndKan.Monitoring.healthCheck

-- Get performance summary
EndKan.Monitoring.getPerformanceSummary
```

## Architecture

### Core Components
- **Pattern Matching Engine**: Sophisticated goal analysis and pattern recognition
- **Transformation Engine**: Mathematical transformation logic with β/η reduction
- **Error Handling System**: Comprehensive error management and recovery
- **Configuration System**: Flexible configuration options

### Production Components
- **Benchmarking System**: Statistical analysis, performance regression detection, and automated testing
- **Telemetry System**: Real-time metrics collection, performance tracking, and alerting
- **Optimization Engine**: Cached pattern matching, optimized data structures, and memory management
- **Configuration Management**: Environment-specific settings, validation, and secure handling
- **Monitoring Dashboard**: Health checks, performance thresholds, and automated alerting

### Performance
- P95 ≤ 500ms on the golden test suite
- Success ≥ 70% on canned naturality/Kan patterns without manual steps
- Deterministic behavior across multiple runs
- Comprehensive benchmarking and testing

### Production Performance
- **Benchmarking**: Statistical analysis with confidence intervals, outlier detection, and regression testing
- **Telemetry**: Real-time performance tracking with P95/P99 metrics and error rate monitoring
- **Optimization**: Cached pattern matching with 80%+ hit rates and memory-efficient data structures
- **Monitoring**: Automated health checks with configurable thresholds and alerting
- **Configuration**: Environment-specific performance tuning with validation and secure handling

## Dependencies

- Lean 4
- mathlib4 categories
- Future minor versions may add enriched variants behind typeclass gates

## License

This project is licensed under the Apache License 2.0.
-/
