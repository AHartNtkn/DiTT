use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn collect_rs_files(root: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_rs_files(&path, out);
            continue;
        }
        if path.extension().and_then(|s| s.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

#[test]
#[ignore = "green-phase readiness contract: enabled when implementations replace stubs"]
fn no_unimplemented_interfaces_remain_in_src() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    collect_rs_files(&root, &mut files);

    let mut offenders = Vec::new();
    for file in files {
        let body = fs::read_to_string(&file).unwrap();
        if body.contains("Unimplemented(\"") || body.contains("LanguageError::Unimplemented") {
            offenders.push(file.display().to_string());
        }
    }
    assert!(
        offenders.is_empty(),
        "green phase requires removing unimplemented stubs: {offenders:?}"
    );
}

#[test]
#[ignore = "green-phase readiness contract: enabled when CI is switched from red phase to green phase"]
fn ci_no_longer_uses_red_phase_gate_as_required_path() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let ci = fs::read_to_string(root.join(".github/workflows/ci.yml")).unwrap();
    assert!(
        !ci.contains("scripts/check_red_phase.sh"),
        "green phase requires removing red-phase gate from required CI workflow"
    );
}

#[test]
#[ignore = "green-phase readiness contract: enabled when full implementation is available"]
fn full_contract_suite_passes_in_green_phase() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let status = Command::new("cargo")
        .args(["test", "--no-fail-fast"])
        .current_dir(root)
        .status()
        .expect("failed to execute cargo test");
    assert!(
        status.success(),
        "green phase requires full contract suite to pass"
    );
}

#[test]
#[ignore = "green-phase readiness contract: enabled when live quality reports are produced in CI"]
fn quality_gates_are_validated_from_live_reports() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let status = Command::new("cargo")
        .args([
            "test",
            "--test",
            "contracts_quality_gate_registry",
            "quality_gate_live_reports_if_present_satisfy_thresholds",
            "--",
            "--nocapture",
        ])
        .env("DITT_QUALITY_REPORT_DIR", "target/quality-reports")
        .env("DITT_REQUIRE_LIVE_REPORTS", "1")
        .current_dir(root)
        .status()
        .expect("failed to execute live quality report contract");
    assert!(
        status.success(),
        "green phase requires live quality report contracts to pass"
    );
}
