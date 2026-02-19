mod common;

use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};
use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

fn stdlib_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("stdlib")
}

fn stdlib_module_paths() -> Vec<PathBuf> {
    let dir = stdlib_dir();
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("cannot read stdlib directory {}: {e}", dir.display()))
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("ditt") {
                Some(path)
            } else {
                None
            }
        })
        .collect();
    paths.sort();
    paths
}

fn read_stdlib_module(path: &PathBuf) -> String {
    fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read stdlib module {}: {e}", path.display()))
}

fn has_named_declaration(source: &str, name: &str) -> bool {
    source.lines().any(|raw| {
        let line = raw.trim_start();
        if line.starts_with("postulate ") {
            return line
                .trim_start_matches("postulate ")
                .split_whitespace()
                .next()
                == Some(name);
        }
        let has_prefix = line.starts_with(name)
            && line[name.len()..]
                .chars()
                .next()
                .map(|c| c == ' ' || c == '(' || c == ':')
                .unwrap_or(false);
        has_prefix && line.contains(':')
    })
}

fn has_definition_body(source: &str, name: &str) -> bool {
    for line in source.lines() {
        let trimmed = line.trim_start();
        let is_named = trimmed.starts_with(name)
            && trimmed[name.len()..]
                .chars()
                .next()
                .map(|c| c == ' ' || c == '(' || c == ':')
                .unwrap_or(false);
        if is_named && trimmed.contains('=') {
            return true;
        }
    }
    false
}

// ─── Registry tests ───

const EXPECTED_MODULES: &[&str] = &[
    "Adjunction",
    "Category",
    "ChurchEncoding",
    "Codensity",
    "EndCoend",
    "Enriched",
    "Functor",
    "KanExtension",
    "Limit",
    "Monad",
    "Morphism",
    "NatTrans",
    "Presheaf",
    "Profunctor",
    "Yoneda",
];

#[test]
fn stdlib_library_modules_are_registered() {
    let paths = stdlib_module_paths();
    let found: BTreeSet<String> = paths
        .iter()
        .filter_map(|p| {
            p.file_stem()
                .and_then(|s| s.to_str())
                .map(|s| s.to_string())
        })
        .collect();
    let expected: BTreeSet<String> = EXPECTED_MODULES.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        found, expected,
        "stdlib/ directory must contain exactly the expected modules.\n  \
         Found:    {found:?}\n  Expected: {expected:?}"
    );
}

// ─── Parse + typecheck tests (will fail with unimplemented!() in red phase) ───

#[test]
fn stdlib_library_modules_parse_and_typecheck() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    for path in stdlib_module_paths() {
        let source = read_stdlib_module(&path);
        let module_name = path.file_stem().unwrap().to_str().unwrap();
        let parsed = syntax
            .parse_module(&source)
            .unwrap_or_else(|e| panic!("stdlib module {module_name} failed to parse: {e:?}"));
        let typed = semantics
            .elaborate_module(&parsed)
            .unwrap_or_else(|e| panic!("stdlib module {module_name} failed to typecheck: {e:?}"));
        assert!(
            !typed.declarations.is_empty(),
            "stdlib module {module_name} has no declarations after elaboration"
        );
    }
}

// ─── Declaration existence tests (text-level, work in red phase) ───

#[test]
fn stdlib_category_defines_id() {
    let source = read_stdlib_module(&stdlib_dir().join("Category.ditt"));
    assert!(
        has_named_declaration(&source, "id"),
        "Std.Category must define 'id'"
    );
}

#[test]
fn stdlib_morphism_defines_compose_and_identity_laws() {
    let source = read_stdlib_module(&stdlib_dir().join("Morphism.ditt"));
    for name in [
        "diag_comp",
        "compose",
        "compose_left_id",
        "compose_right_id",
        "compose_assoc",
        "op_hom_forward",
        "op_hom_backward",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Morphism must define '{name}'"
        );
    }
}

#[test]
fn stdlib_functor_defines_map_and_laws() {
    let source = read_stdlib_module(&stdlib_dir().join("Functor.ditt"));
    for name in ["map_F", "map_id", "map_compose"] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Functor must define '{name}'"
        );
    }
}

#[test]
fn stdlib_nat_trans_defines_composition() {
    let source = read_stdlib_module(&stdlib_dir().join("NatTrans.ditt"));
    for name in [
        "nat_trans",
        "nat_id",
        "nat_comp",
        "whisker_left",
        "whisker_right",
        "poly_id",
        "horizontal_comp",
        "dinat",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.NatTrans must define '{name}'"
        );
    }
}

#[test]
fn stdlib_yoneda_defines_forward_and_backward() {
    let source = read_stdlib_module(&stdlib_dir().join("Yoneda.ditt"));
    for name in [
        "transport_P",
        "yoneda_forward",
        "yoneda_backward",
        "yoneda_roundtrip",
        "yoneda_roundtrip_2",
        "yo",
        "yoneda_ff_forward",
        "yoneda_ff_backward",
        "precompose",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Yoneda must define '{name}'"
        );
    }
}

#[test]
fn stdlib_end_coend_defines_fubini() {
    let source = read_stdlib_module(&stdlib_dir().join("EndCoend.ditt"));
    for name in [
        "end_to_coend",
        "end_preserves_prod_left",
        "end_preserves_prod_right",
        "fubini_left",
        "fubini_right",
        "restricted_cut",
        "singleton",
        "curry_end",
        "uncurry_end",
        "end_preserves_impl_fwd",
        "end_preserves_impl_bwd",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.EndCoend must define '{name}'"
        );
    }
}

#[test]
fn stdlib_kan_extension_defines_ran_and_lan() {
    let source = read_stdlib_module(&stdlib_dir().join("KanExtension.ditt"));
    for name in ["ran", "lan", "ran_unit", "ran_counit", "lan_unit"] {
        assert!(
            has_named_declaration(&source, name),
            "Std.KanExtension must define '{name}'"
        );
    }
}

#[test]
fn stdlib_adjunction_defines_unit_and_counit() {
    let source = read_stdlib_module(&stdlib_dir().join("Adjunction.ditt"));
    for name in [
        "adjoint_forward",
        "adjoint_backward",
        "adjunction_iso",
        "unit",
        "counit",
        "triangle1_composite",
        "triangle2_composite",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Adjunction must define '{name}'"
        );
    }
}

#[test]
fn stdlib_profunctor_defines_composition() {
    let source = read_stdlib_module(&stdlib_dir().join("Profunctor.ditt"));
    for name in [
        "hom_profunctor",
        "prof_compose",
        "prof_id_witness",
        "repr_profunctor",
        "rift",
        "nat_prof",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Profunctor must define '{name}'"
        );
    }
}

#[test]
fn stdlib_codensity_defines_monad_structure() {
    let source = read_stdlib_module(&stdlib_dir().join("Codensity.ditt"));
    for name in [
        "codensity",
        "codensity_unit",
        "codensity_counit",
        "codensity_join",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Codensity must define '{name}'"
        );
    }
}

#[test]
fn stdlib_presheaf_defines_exponential() {
    let source = read_stdlib_module(&stdlib_dir().join("Presheaf.ditt"));
    for name in [
        "presheaf_exp",
        "presheaf_eval",
        "presheaf_curry",
        "day_conv",
        "day_unit",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Presheaf must define '{name}'"
        );
    }
}

#[test]
fn stdlib_church_encoding_defines_booleans_naturals_and_cross_type() {
    let source = read_stdlib_module(&stdlib_dir().join("ChurchEncoding.ditt"));
    for name in [
        "BoolCP",
        "trueCP",
        "falseCP",
        "ifCP",
        "andCP",
        "orCP",
        "notCP",
        "NatCP",
        "zero",
        "succ",
        "add",
        "mult",
        "iterate",
        "isZero",
        "boolToNat",
        "ifNat",
        "ListAP",
        "nil",
        "cons",
        "foldr",
        "append",
        "MaybeAP",
        "nothingAP",
        "justAP",
        "maybeAP",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.ChurchEncoding must define '{name}'"
        );
    }
}

// ─── Structural tests ───

#[test]
fn stdlib_library_modules_have_no_duplicate_declarations() {
    for path in stdlib_module_paths() {
        let source = read_stdlib_module(&path);
        let module_name = path.file_stem().unwrap().to_str().unwrap();
        let mut decl_names = BTreeSet::new();
        for line in source.lines() {
            let trimmed = line.trim_start();
            // Skip blank lines, comments, keywords-only lines, and language keywords
            // that appear as the first token of type-expression continuation lines.
            if trimmed.is_empty()
                || trimmed.starts_with("//")
                || trimmed.starts_with("module ")
                || trimmed.starts_with("import ")
                || trimmed == "postulate"
                || trimmed == "where"
                || trimmed.starts_with("end ")
                || trimmed.starts_with("end(")
                || trimmed.starts_with("coend ")
                || trimmed.starts_with("coend(")
                || trimmed.starts_with('\\')
                || trimmed.starts_with('(')
                || trimmed.starts_with(')')
                || trimmed.starts_with('.')
            {
                continue;
            }
            // Inside postulate block: "name : type"
            if trimmed.contains(':') && !trimmed.contains('=') && !trimmed.starts_with("postulate ")
            {
                if let Some(name) = trimmed.split_whitespace().next()
                    && name
                        .chars()
                        .next()
                        .map(|c| c.is_alphabetic())
                        .unwrap_or(false)
                {
                    assert!(
                        decl_names.insert(name.to_string()),
                        "duplicate declaration '{name}' in stdlib module {module_name}"
                    );
                }
                continue;
            }
            // Postulate on one line: "postulate name : type"
            if trimmed.starts_with("postulate ") {
                if let Some(name) = trimmed
                    .trim_start_matches("postulate ")
                    .split_whitespace()
                    .next()
                {
                    assert!(
                        decl_names.insert(name.to_string()),
                        "duplicate declaration '{name}' in stdlib module {module_name}"
                    );
                }
                continue;
            }
            // Definition: "name (args) : type = body" or "name : type = body"
            if let Some(name) = trimmed.split_whitespace().next()
                && name
                    .chars()
                    .next()
                    .map(|c| c.is_alphabetic())
                    .unwrap_or(false)
                && trimmed.contains(':')
            {
                assert!(
                    decl_names.insert(name.to_string()),
                    "duplicate declaration '{name}' in stdlib module {module_name}"
                );
            }
        }
    }
}

#[test]
fn stdlib_limit_defines_cones_and_weighted() {
    let source = read_stdlib_module(&stdlib_dir().join("Limit.ditt"));
    for name in [
        "limit_cone",
        "colimit_cocone",
        "limit_property",
        "colimit_property",
        "weighted_limit",
        "weighted_colimit",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Limit must define '{name}'"
        );
    }
}

#[test]
fn stdlib_monad_defines_structure() {
    let source = read_stdlib_module(&stdlib_dir().join("Monad.ditt"));
    for name in [
        "monad_unit_type",
        "monad_mult_type",
        "map_T",
        "algebra",
        "free_algebra",
        "comonad_counit_type",
        "comonad_comult_type",
        "map_W",
        "coalgebra",
        "adjunction_mult",
    ] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Monad must define '{name}'"
        );
    }
}

#[test]
fn stdlib_enriched_defines_v_structure() {
    let source = read_stdlib_module(&stdlib_dir().join("Enriched.ditt"));
    for name in ["v_functor_action", "v_nat_trans"] {
        assert!(
            has_named_declaration(&source, name),
            "Std.Enriched must define '{name}'"
        );
    }
}

// ─── Structural tests ───

#[test]
fn stdlib_library_all_definitions_have_bodies() {
    for path in stdlib_module_paths() {
        let source = read_stdlib_module(&path);
        let module_name = path.file_stem().unwrap().to_str().unwrap();

        // Collect postulate names (these are allowed to lack bodies)
        let mut postulate_names = BTreeSet::new();
        let mut in_postulate_block = false;
        for line in source.lines() {
            let trimmed = line.trim_start();
            if trimmed == "postulate" {
                in_postulate_block = true;
                continue;
            }
            if in_postulate_block {
                if trimmed.is_empty() || trimmed.starts_with("//") {
                    continue;
                }
                // A non-indented line ends the postulate block
                if !line.starts_with(' ') && !line.starts_with('\t') && !trimmed.is_empty() {
                    in_postulate_block = false;
                } else if let Some(name) = trimmed.split_whitespace().next() {
                    postulate_names.insert(name.to_string());
                    continue;
                }
            }
            if trimmed.starts_with("postulate ")
                && let Some(name) = trimmed
                    .trim_start_matches("postulate ")
                    .split_whitespace()
                    .next()
            {
                postulate_names.insert(name.to_string());
            }
        }

        // Check that non-postulate declarations have '=' (a body)
        for line in source.lines() {
            let trimmed = line.trim_start();
            if trimmed.is_empty()
                || trimmed.starts_with("//")
                || trimmed.starts_with("module ")
                || trimmed.starts_with("import ")
                || trimmed.starts_with("postulate")
                || trimmed == "where"
            {
                continue;
            }
            // Skip lines inside postulate blocks (indented after "postulate")
            if line.starts_with(' ') || line.starts_with('\t') {
                // Could be inside a postulate block or a continuation
                continue;
            }
            if let Some(name) = trimmed.split_whitespace().next()
                && name
                    .chars()
                    .next()
                    .map(|c| c.is_alphabetic())
                    .unwrap_or(false)
                && trimmed.contains(':')
                && !postulate_names.contains(name)
            {
                assert!(
                    has_definition_body(&source, name),
                    "non-postulate declaration '{name}' in stdlib module {module_name} must have a body (=)"
                );
            }
        }
    }
}
