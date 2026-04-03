use clap::{Parser, Subcommand};
use endkan::*;
use std::time::Duration;
use tokio::time::sleep;

#[derive(Parser)]
#[command(name = "endkan")]
#[command(about = "EndKan Rust helper: health checks, demo benchmarks, simple monitoring")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Run demo test suite
    Test,
    /// Poll demo monitoring output
    Monitor,
    /// Run benchmarks
    Benchmark {
        /// Number of iterations
        #[arg(short, long, default_value = "1000")]
        iterations: usize,
    },
    /// Check system health
    Health,
    /// Generate monitoring report
    Report,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize logging
    tracing_subscriber::fmt::init();

    let cli = Cli::parse();

    let config = ProductionConfig {
        performance: PerformanceConfig {
            timeout_ms: 5000,
            max_memory_mb: 1000,
            max_cpu_percent: 80.0,
            enable_profiling: true,
        },
        telemetry: TelemetryConfig {
            enabled: true,
            sampling_rate: 1.0,
            batch_size: 100,
            flush_interval_ms: 5000,
        },
        monitoring: MonitoringConfig {
            health_check_interval_ms: 1000,
            alert_thresholds: AlertThresholds {
                max_response_time_ms: 1000,
                max_error_rate: 0.05,
                max_memory_usage_mb: 1000,
                max_cpu_usage_percent: 80.0,
                min_cache_hit_rate: 0.8,
            },
            enable_dashboard: true,
        },
        caching: CachingConfig {
            enabled: true,
            max_size: 1000,
            ttl_seconds: 3600,
            enable_compression: true,
        },
    };

    let system = ProductionSystem::new(config);
    system.initialize().await;

    match cli.command {
        Commands::Test => {
            println!("Running EndKan demo test suite...");
            system.run_production_tests().await;
        }
        Commands::Monitor => {
            println!("Starting EndKan demo monitoring loop...");
            println!("Press Ctrl+C to stop");

            loop {
                let health = system.monitoring.check_health().await;
                println!("Health check: {}", health);

                let (cache_size, hit_rate) = system.caching.get_stats();
                println!(
                    "Cache: {} entries, {:.1}% hit rate",
                    cache_size,
                    hit_rate * 100.0
                );

                sleep(Duration::from_secs(5)).await;
            }
        }
        Commands::Benchmark { iterations } => {
            println!(
                "Running EndKan benchmarks with {} iterations...",
                iterations
            );
            let stats = system.benchmarking.run_benchmark_suite(iterations).await;

            println!("\nBenchmark Results:");
            println!("==================");
            println!("Mean execution time: {:.2}ms", stats.mean);
            println!("Median execution time: {:.2}ms", stats.median);
            println!("Standard deviation: {:.2}ms", stats.std_dev);
            println!("P95 execution time: {:.2}ms", stats.p95);
            println!("P99 execution time: {:.2}ms", stats.p99);
            println!("Sample size: {}", stats.sample_size);
            println!(
                "95% Confidence interval: ({:.2}, {:.2})",
                stats.confidence_interval_95.0, stats.confidence_interval_95.1
            );

            if !stats.outliers.is_empty() {
                println!("Outliers detected: {}", stats.outliers.len());
            }
        }
        Commands::Health => {
            let health = system.monitoring.check_health().await;
            println!("System Health: {}", health);
        }
        Commands::Report => {
            let report = system.monitoring.generate_report().await;
            println!("{}", report);
        }
    }

    Ok(())
}
