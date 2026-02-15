use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn collect_ditt_targets(root: &Path) -> BTreeSet<String> {
    fn walk(path: &Path, out: &mut BTreeSet<String>, base: &Path) {
        for entry in fs::read_dir(path).unwrap() {
            let p = entry.unwrap().path();
            if p.is_dir() {
                walk(&p, out, base);
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) == Some("ditt") {
                out.insert(p.strip_prefix(base).unwrap().to_string_lossy().to_string());
            }
        }
    }

    let mut out = BTreeSet::new();
    walk(&root.join("tests").join("conformance"), &mut out, root);
    out
}

fn collect_doc_targets(root: &Path) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for entry in fs::read_dir(root.join("docs")).unwrap() {
        let p = entry.unwrap().path();
        if p.is_dir() {
            continue;
        }
        let ext = p.extension().and_then(|s| s.to_str());
        if !matches!(ext, Some("csv") | Some("md")) {
            continue;
        }
        let rel = p.strip_prefix(root).unwrap().to_string_lossy().to_string();
        if rel != "docs/CORPUS_LOCK.csv" {
            out.insert(rel);
        }
    }
    out
}

fn sha256(root: &Path, rel: &str) -> String {
    let path = root.join(rel);
    let run = |program: &str, args: &[&str]| -> Option<String> {
        let output = Command::new(program).args(args).output().ok()?;
        if !output.status.success() {
            return None;
        }
        let text = String::from_utf8(output.stdout).ok()?;
        let digest = text.split_whitespace().next()?.to_string();
        if digest.len() == 64 {
            Some(digest)
        } else {
            None
        }
    };

    run("sha256sum", &[path.to_str().unwrap()])
        .or_else(|| run("shasum", &["-a", "256", path.to_str().unwrap()]))
        .unwrap_or_else(|| panic!("failed to compute sha256 for {rel}"))
}

fn size_bytes(root: &Path, rel: &str) -> u64 {
    fs::metadata(root.join(rel))
        .unwrap_or_else(|_| panic!("failed to stat {rel}"))
        .len()
}

#[test]
fn corpus_lock_matches_current_ditt_fixture_digests_and_docs_exist() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let body = fs::read_to_string(root.join("docs").join("CORPUS_LOCK.csv")).unwrap();
    let mut lines = body.lines().filter(|l| !l.trim().is_empty());
    let header = lines
        .next()
        .unwrap_or_default()
        .split(',')
        .map(|s| s.trim())
        .collect::<Vec<_>>();
    assert_eq!(header, vec!["path", "sha256", "size"]);

    let mut ditt_from_lock = BTreeSet::new();
    for line in lines {
        let cols = line.split(',').map(|s| s.trim()).collect::<Vec<_>>();
        assert_eq!(cols.len(), 3, "bad lock row: {line}");
        let rel = cols[0];
        let expected_sha256 = cols[1];
        let expected_size = cols[2];

        assert!(
            root.join(rel).exists(),
            "lock references missing file: {rel}"
        );

        if rel.ends_with(".ditt") {
            let actual_sha256 = sha256(&root, rel);
            let actual_size = size_bytes(&root, rel).to_string();
            assert_eq!(actual_sha256, expected_sha256, "digest drift for {rel}");
            assert_eq!(actual_size, expected_size, "size drift for {rel}");
            assert!(
                ditt_from_lock.insert(rel.to_string()),
                "duplicate lock path: {rel}"
            );
        }
    }

    let expected_ditt_targets = collect_ditt_targets(&root);
    assert_eq!(
        ditt_from_lock, expected_ditt_targets,
        "corpus lock must track exactly the .ditt fixture set"
    );

    for rel in collect_doc_targets(&root) {
        let size = size_bytes(&root, &rel);
        assert!(size > 0, "docs corpus file must be non-empty: {rel}");
    }
}
