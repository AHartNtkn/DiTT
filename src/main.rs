use std::collections::BTreeMap;
use std::io::{self, BufRead, Read, Write};
use std::process;

use ditt_lang::api::*;
use ditt_lang::runtime::ToolingEngine;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    if args.is_empty() {
        print_usage();
        process::exit(1);
    }

    match args[0].as_str() {
        "repl" => run_repl(),
        "help" | "--help" | "-h" => {
            print_usage();
        }
        _ => run_command(args),
    }
}

fn run_command(args: Vec<String>) {
    let command = &args[0];
    let needs_source = matches!(command.as_str(), "check" | "build" | "fmt" | "run");

    let (engine_args, source) = if needs_source {
        separate_file_arg(&args)
    } else {
        (args, String::new())
    };

    let tooling = ToolingEngine::default();
    let invocation = CliInvocation {
        args: engine_args,
        stdin: source,
        env: std::env::vars().collect::<BTreeMap<_, _>>(),
    };

    match tooling.invoke(&invocation) {
        Ok(response) => {
            if !response.stdout.is_empty() {
                print!("{}", response.stdout);
            }
            if !response.stderr.is_empty() {
                eprint!("{}", response.stderr);
            }
            process::exit(response.exit_code);
        }
        Err(err) => {
            print_diagnostics(&err.into_diagnostics());
            process::exit(1);
        }
    }
}

/// Separate a file path argument from CLI flags/options.
///
/// Commands that accept source (`check`, `build`, `fmt`, `run`) can take an
/// optional file path as a positional argument. This function finds it, reads
/// the file, and returns the remaining engine-level args plus the source text.
/// If no file path is found, source is read from stdin.
fn separate_file_arg(args: &[String]) -> (Vec<String>, String) {
    let mut engine_args = Vec::new();
    let mut file_path: Option<String> = None;

    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        if arg.starts_with("--") {
            engine_args.push(arg.clone());
            // Valued options: consume the next arg too.
            if (arg == "--entry" || arg == "--normalize") && i + 1 < args.len() {
                engine_args.push(args[i + 1].clone());
                i += 2;
            } else {
                i += 1;
            }
        } else if i == 0 {
            // The command name itself.
            engine_args.push(arg.clone());
            i += 1;
        } else if file_path.is_none() {
            file_path = Some(arg.clone());
            i += 1;
        } else {
            eprintln!("error: unexpected argument '{}'", arg);
            process::exit(1);
        }
    }

    let source = if let Some(path) = file_path {
        match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(err) => {
                eprintln!("error: cannot read '{}': {}", path, err);
                process::exit(1);
            }
        }
    } else {
        let mut buf = String::new();
        io::stdin().read_to_string(&mut buf).unwrap_or_default();
        buf
    };

    (engine_args, source)
}

fn run_repl() {
    let mut tooling = ToolingEngine::default();
    let session = match Repl::start_session(&mut tooling) {
        Ok(s) => s,
        Err(err) => {
            print_diagnostics(&err.into_diagnostics());
            process::exit(1);
        }
    };

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = stdout.lock();

    let _ = writeln!(out, "DiTT 0.1.0 — :load <file>, :help, :quit");
    let _ = write!(out, "> ");
    let _ = out.flush();

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };

        let trimmed = line.trim();
        if trimmed == ":quit" || trimmed == ":q" {
            break;
        }

        if let Some(path) = trimmed.strip_prefix(":load ").map(str::trim) {
            match std::fs::read_to_string(path) {
                Ok(source) => match Repl::submit(&mut tooling, session, &source) {
                    Ok(output) => {
                        if output.diagnostics.diagnostics.is_empty() {
                            let _ = writeln!(out, "Loaded {}", path);
                        }
                        for diag in &output.diagnostics.diagnostics {
                            let _ = writeln!(out, "[{}] {}", diag.category, diag.message);
                        }
                    }
                    Err(err) => print_diagnostics(&err.into_diagnostics()),
                },
                Err(err) => {
                    let _ = writeln!(out, "error: cannot read '{}': {}", path, err);
                }
            }
            let _ = write!(out, "> ");
            let _ = out.flush();
            continue;
        }

        if trimmed == ":help" {
            let _ = writeln!(out, "  :load <file>   Load a .ditt module");
            let _ = writeln!(out, "  :quit          Exit the REPL");
            let _ = write!(out, "> ");
            let _ = out.flush();
            continue;
        }

        match Repl::submit(&mut tooling, session, trimmed) {
            Ok(output) => {
                if !output.rendered.is_empty() {
                    let _ = writeln!(out, "{}", output.rendered);
                }
                for diag in &output.diagnostics.diagnostics {
                    let _ = writeln!(out, "[{}] {}", diag.category, diag.message);
                }
            }
            Err(err) => {
                print_diagnostics(&err.into_diagnostics());
            }
        }

        let _ = write!(out, "> ");
        let _ = out.flush();
    }

    let _ = Repl::end_session(&mut tooling, session);
}

fn print_diagnostics(bundle: &DiagnosticBundle) {
    for diag in &bundle.diagnostics {
        eprintln!("[{}] {}", diag.category, diag.message);
    }
}

fn print_usage() {
    eprintln!(
        "\
DiTT — Directed Type Theory

Usage: ditt <command> [options] [file]

Commands:
  check       Type-check a module
  build       Build (type-check) a module
  fmt         Format a module
  run         Evaluate or normalize a definition
  repl        Start an interactive REPL
  lsp         Start the language server
  notebook    Jupyter notebook kernel

Options:
  --json           Machine-readable JSON output
  --check          (fmt) Check formatting without modifying
  --entry <name>   (run) Evaluate a definition
  --normalize <name> (run) Normalize a definition

If no file is given, source is read from stdin."
    );
}
