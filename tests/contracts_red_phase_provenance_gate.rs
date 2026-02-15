use std::fs;
use std::path::PathBuf;

#[test]
fn red_phase_provenance_gate_script_is_present_and_wired() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let provenance = root.join("scripts/check_red_phase_provenance.sh");
    let bridge = root.join("scripts/check_red_phase.sh");

    assert!(provenance.exists(), "missing red-phase provenance script");
    let provenance_body = fs::read_to_string(&provenance).unwrap();
    assert!(!provenance_body.trim().is_empty());
    assert!(provenance_body.contains("cargo test --no-fail-fast"));
    assert!(provenance_body.contains("not implemented:"));
    assert!(provenance_body.contains("did not show unimplemented provenance"));

    assert!(bridge.exists(), "missing red-phase bridge script");
    let bridge_body = fs::read_to_string(&bridge).unwrap();
    assert!(bridge_body.contains("check_red_phase_provenance.sh"));
}
