use std::fs;
use std::path::PathBuf;

#[test]
fn quality_gate_scripts_are_present() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let scripts = [
        "scripts/check_mutation_gate.sh",
        "scripts/fuzz_smoke.sh",
        "scripts/run_perf_contracts.sh",
        "scripts/run_quality_contracts_live.sh",
    ];

    for script in scripts {
        let path = root.join(script);
        assert!(path.exists(), "missing quality gate script: {script}");
        let body = fs::read_to_string(path).unwrap();
        assert!(
            !body.trim().is_empty(),
            "quality gate script is empty: {script}"
        );
    }
}

fn kv(body: &str) -> Vec<(&str, &str)> {
    body.lines()
        .filter_map(|line| line.split_once('='))
        .map(|(k, v)| (k.trim(), v.trim()))
        .collect::<Vec<_>>()
}

fn parse_mutation_score(body: &str) -> u64 {
    let score_line = body
        .lines()
        .find(|line| line.contains("\"mutation_score\""))
        .expect("missing mutation_score");
    score_line
        .split(':')
        .nth(1)
        .expect("missing mutation score value")
        .trim()
        .trim_end_matches(',')
        .parse::<u64>()
        .expect("bad mutation score")
}

#[test]
fn mutation_report_sample_meets_threshold_contract() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body =
        fs::read_to_string(root.join("tests/conformance/quality/mutation_report_sample.json"))
            .unwrap();
    let score = parse_mutation_score(&body);
    let threshold = 80u64;
    assert!(
        score >= threshold,
        "mutation score {} below threshold {}",
        score,
        threshold
    );
}

fn check_fuzz_report_common(body: &str, allow_skipped: bool) {
    let mut current_target = None::<String>;
    let mut seen_targets = std::collections::BTreeSet::new();
    let mut saw_skipped = false;
    for (k, v) in kv(body) {
        match k {
            "target" => {
                current_target = Some(v.to_string());
                seen_targets.insert(v.to_string());
            }
            "status" => {
                if allow_skipped && v == "skipped" {
                    saw_skipped = true;
                } else {
                    assert_eq!(v, "ok");
                }
            }
            "crashes" | "timeouts" => assert_eq!(v, "0"),
            "executions" => {
                let execs = v.parse::<u64>().expect("bad executions count");
                if saw_skipped {
                    assert_eq!(execs, 0, "skipped fuzz report must have zero executions");
                } else {
                    assert!(execs > 0, "executions must be nonzero");
                }
            }
            _ => panic!("unexpected key in fuzz report"),
        }
    }
    assert!(current_target.is_some(), "empty fuzz report");
    if !saw_skipped {
        let required = ["parser", "cli_protocol", "lsp_protocol"];
        for target in required {
            assert!(
                seen_targets.contains(target),
                "missing fuzz report target: {target}"
            );
        }
    }
}

#[test]
fn fuzz_report_sample_has_no_crashes_or_timeouts_for_required_targets() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body =
        fs::read_to_string(root.join("tests/conformance/quality/fuzz_report_sample.txt")).unwrap();
    check_fuzz_report_common(&body, false);
}

fn check_perf_report_common(body: &str, required_metrics: &[&str]) {
    let mut current_metric = None::<String>;
    let mut current_value = None::<u64>;
    let mut seen_metrics = std::collections::BTreeSet::new();

    for (k, v) in kv(body) {
        match k {
            "metric" => {
                current_metric = Some(v.to_string());
                seen_metrics.insert(v.to_string());
                current_value = None;
            }
            "value" => {
                current_value = Some(v.parse::<u64>().expect("bad value"));
            }
            "budget" => {
                let value = current_value.expect("budget without value");
                let budget = v.parse::<u64>().expect("bad budget");
                assert!(
                    value <= budget,
                    "metric {} exceeds budget: {} > {}",
                    current_metric.as_deref().unwrap_or("<unknown>"),
                    value,
                    budget
                );
            }
            _ => panic!("unexpected key in perf report"),
        }
    }

    for metric in required_metrics {
        assert!(
            seen_metrics.contains(*metric),
            "missing perf metric: {metric}"
        );
    }
}

#[test]
fn perf_report_sample_respects_budget_thresholds() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body =
        fs::read_to_string(root.join("tests/conformance/quality/perf_report_sample.txt")).unwrap();
    check_perf_report_common(&body, &["parse_p95_ms", "check_p95_ms", "normalize_p95_ms"]);
}

#[test]
fn quality_gate_live_reports_if_present_satisfy_thresholds() {
    let Some(dir) = std::env::var("DITT_QUALITY_REPORT_DIR").ok() else {
        return;
    };
    let require = std::env::var("DITT_REQUIRE_LIVE_REPORTS")
        .ok()
        .map(|v| v == "1")
        .unwrap_or(false);
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(dir);

    let mut seen_any = false;

    let mutation = root.join("mutation_report.json");
    if mutation.exists() {
        seen_any = true;
        let body = fs::read_to_string(mutation).unwrap();
        let score = parse_mutation_score(&body);
        let threshold = 80u64;
        assert!(score >= threshold, "live mutation score below threshold");
    }

    let fuzz = root.join("fuzz_report.txt");
    if fuzz.exists() {
        seen_any = true;
        let body = fs::read_to_string(fuzz).unwrap();
        check_fuzz_report_common(&body, true);
    }

    let perf = root.join("perf_report.txt");
    if perf.exists() {
        seen_any = true;
        let body = fs::read_to_string(perf).unwrap();
        let has_metric = body.lines().any(|line| line.trim().starts_with("metric="));
        assert!(has_metric, "live perf report has no metrics");
        check_perf_report_common(
            &body,
            &[
                "parse_ms",
                "check_ms",
                "normalize_ms",
                "lsp_incremental_diagnostics_ms",
                "cli_check_json_ms",
            ],
        );
    }

    if require {
        assert!(
            seen_any,
            "DITT_REQUIRE_LIVE_REPORTS=1 but no live reports found"
        );
    }
}
