use std::collections::{BTreeSet, HashMap, HashSet};

use crate::api::*;

use super::{SemanticEngine, SyntaxEngine};

const BASE_COMPLETIONS: &[&str] = &[
    "module",
    "import",
    "postulate",
    "where",
    "let",
    "in",
    "refl",
    "J",
    "end",
    "coend",
    "Cat",
    "Prop",
    "Top",
];

#[derive(Debug, Clone, Default)]
struct SessionState {
    snippets: Vec<String>,
    typed: Option<TypedModule>,
    history: Vec<String>,
    interrupted: bool,
}

#[derive(Debug, Clone, Default)]
struct DocumentState {
    text: String,
    saved: bool,
}

#[derive(Debug, Default)]
pub struct ToolingEngine {
    syntax: SyntaxEngine,
    semantics: SemanticEngine,
    next_session: SessionId,
    execution_counter: u64,
    sessions: HashMap<SessionId, SessionState>,
    documents: HashMap<String, DocumentState>,
    cancelled_requests: HashSet<RequestId>,
    kernel_shutdown: bool,
}

impl ModuleSystem for ToolingEngine {
    fn build_graph(&self, modules: &[ModuleText]) -> Result<ModuleGraph, LanguageError> {
        let mut seen = HashSet::new();
        for module in modules {
            if !seen.insert(module.name.clone()) {
                return Err(module_system_error(
                    "duplicate_module",
                    format!("duplicate module name '{}'", module.name),
                ));
            }
        }

        let mut edges = Vec::new();
        for module in modules {
            let parsed = self
                .syntax
                .parse_module(&module.source)
                .map_err(module_error_from_bundle)?;
            let from = ModuleId(module.name.clone());
            for import in parsed.imports {
                edges.push((
                    from.clone(),
                    ModuleId(import.path.to_string()),
                    ImportSpec {
                        alias: import.alias,
                        filter: import.filter,
                        renamings: import.renamings,
                    },
                ));
            }
        }

        Ok(ModuleGraph {
            modules: modules
                .iter()
                .map(|m| ModuleId(m.name.clone()))
                .collect::<Vec<_>>(),
            edges,
        })
    }
}

impl Cli for ToolingEngine {
    fn invoke(&self, invocation: &CliInvocation) -> Result<CliResponse, LanguageError> {
        let json_mode = invocation.args.iter().any(|arg| arg == "--json");
        if invocation.args.is_empty() {
            return Ok(cli_error_response(
                json_mode,
                "no command provided",
                diagnostic(
                    "Cli",
                    "missing_command",
                    "no command provided".to_string(),
                    None,
                ),
            ));
        }

        let command = invocation.args[0].as_str();
        match command {
            "check" => self.invoke_check(invocation),
            "build" => self.invoke_build(invocation),
            "fmt" => self.invoke_fmt(invocation),
            "run" => self.invoke_run(invocation),
            "repl" => self.invoke_repl(invocation),
            "lsp" => self.invoke_lsp(invocation),
            "notebook" => self.invoke_notebook(invocation),
            other => Ok(cli_error_response(
                json_mode,
                format!("unknown command '{}'", other),
                diagnostic(
                    "Cli",
                    "unknown_command",
                    format!("unknown command '{}'", other),
                    None,
                ),
            )),
        }
    }
}

impl Repl for ToolingEngine {
    fn start_session(&mut self) -> Result<SessionId, LanguageError> {
        self.next_session = self.next_session.saturating_add(1);
        let session = self.next_session;
        self.sessions.entry(session).or_default();
        Ok(session)
    }

    fn submit(&mut self, session: SessionId, input: &str) -> Result<ReplOutput, LanguageError> {
        let mut state = self
            .sessions
            .get(&session)
            .cloned()
            .ok_or_else(|| repl_error("unknown session id".to_string(), ReplPhase::Submit))?;
        let trimmed = input.trim();

        if trimmed.starts_with(':') {
            return Ok(ReplOutput {
                rendered: String::new(),
                diagnostics: DiagnosticBundle::default(),
            });
        }

        if is_full_module_source(trimmed) {
            match self.compile_checked_source(trimmed) {
                Ok((_parsed, typed)) => {
                    state.snippets = vec![trimmed.to_string()];
                    state.typed = Some(typed);
                    self.sessions.insert(session, state);
                    return Ok(ReplOutput {
                        rendered: String::new(),
                        diagnostics: DiagnosticBundle::default(),
                    });
                }
                Err(diagnostics) => {
                    return Ok(ReplOutput {
                        rendered: String::new(),
                        diagnostics,
                    });
                }
            }
        }

        if looks_like_declaration(trimmed) {
            let candidate = source_with_appended_snippet(session, &state.snippets, trimmed);
            match self.compile_checked_source(&candidate) {
                Ok((_parsed, typed)) => {
                    state.snippets.push(trimmed.to_string());
                    state.typed = Some(typed);
                    self.sessions.insert(session, state);
                    return Ok(ReplOutput {
                        rendered: String::new(),
                        diagnostics: DiagnosticBundle::default(),
                    });
                }
                Err(diagnostics) => {
                    return Ok(ReplOutput {
                        rendered: String::new(),
                        diagnostics,
                    });
                }
            }
        }

        let typed = match &state.typed {
            Some(typed) => typed.clone(),
            None => {
                let base_source = render_session_source(session, &state.snippets);
                match self.compile_checked_source(&base_source) {
                    Ok((_parsed, typed)) => typed,
                    Err(diagnostics) => {
                        return Ok(ReplOutput {
                            rendered: String::new(),
                            diagnostics,
                        });
                    }
                }
            }
        };

        let expr = match self.syntax.parse_expr(trimmed) {
            Ok(expr) => expr,
            Err(err) => {
                return Ok(ReplOutput {
                    rendered: String::new(),
                    diagnostics: err.into_diagnostics(),
                });
            }
        };

        match self.semantics.evaluate_term(&typed, &expr) {
            Ok(outcome) => {
                self.sessions.insert(session, state);
                Ok(ReplOutput {
                    rendered: outcome.value,
                    diagnostics: DiagnosticBundle::default(),
                })
            }
            Err(err) => Ok(ReplOutput {
                rendered: String::new(),
                diagnostics: err.into_diagnostics(),
            }),
        }
    }

    fn complete(&self, session: SessionId, prefix: &str) -> Result<Vec<String>, LanguageError> {
        let state = self
            .sessions
            .get(&session)
            .ok_or_else(|| repl_error("unknown session id".to_string(), ReplPhase::Complete))?;
        let mut candidates = BTreeSet::new();
        for item in BASE_COMPLETIONS {
            candidates.insert((*item).to_string());
        }
        if let Some(typed) = &state.typed {
            for decl in &typed.declarations {
                candidates.insert(decl.declaration.name().to_string());
            }
        }
        Ok(candidates
            .into_iter()
            .filter(|item| item.starts_with(prefix))
            .collect::<Vec<_>>())
    }

    fn end_session(&mut self, session: SessionId) -> Result<(), LanguageError> {
        if self.sessions.remove(&session).is_some() {
            Ok(())
        } else {
            Err(repl_error("unknown session id".to_string(), ReplPhase::End))
        }
    }
}

impl NotebookKernel for ToolingEngine {
    fn kernel_info(&self) -> Result<KernelInfo, LanguageError> {
        Ok(KernelInfo {
            language_name: "DiTT".to_string(),
            language_version: "0.1.0".to_string(),
            mimetype: "text/x-ditt".to_string(),
            file_extension: ".ditt".to_string(),
            banner: "DiTT notebook kernel".to_string(),
        })
    }

    fn execute(&mut self, request: &ExecuteRequest) -> Result<ExecuteReply, LanguageError> {
        if self.kernel_shutdown {
            return Err(notebook_error(
                "kernel is shut down".to_string(),
                NotebookPhase::Execute,
            ));
        }
        if contains_unsafe_primitive(&request.code) {
            return Err(notebook_error(
                "unsafe filesystem or network primitive".to_string(),
                NotebookPhase::Execute,
            ));
        }

        self.execution_counter = self.execution_counter.saturating_add(1);
        let execution_count = self.execution_counter;
        let mut state = self
            .sessions
            .get(&request.session)
            .cloned()
            .unwrap_or_default();
        state.interrupted = false;
        if request.store_history {
            state.history.push(request.code.clone());
        }

        let trimmed = request.code.trim();
        if is_full_module_source(trimmed) {
            match self.compile_checked_source(trimmed) {
                Ok((_parsed, typed)) => {
                    state.snippets = vec![trimmed.to_string()];
                    state.typed = Some(typed);
                    self.sessions.insert(request.session, state);
                    return Ok(ExecuteReply {
                        status: ExecutionStatus::Ok,
                        execution_count,
                        events: notebook_events_ok(request.silent, "ok".to_string()),
                    });
                }
                Err(diagnostics) => {
                    self.sessions.insert(request.session, state);
                    return Ok(ExecuteReply {
                        status: ExecutionStatus::Error,
                        execution_count,
                        events: notebook_events_error(request.silent, &diagnostics),
                    });
                }
            }
        }

        if looks_like_declaration(trimmed) {
            let candidate = source_with_appended_snippet(request.session, &state.snippets, trimmed);
            match self.compile_checked_source(&candidate) {
                Ok((_parsed, typed)) => {
                    state.snippets.push(trimmed.to_string());
                    state.typed = Some(typed);
                    self.sessions.insert(request.session, state);
                    return Ok(ExecuteReply {
                        status: ExecutionStatus::Ok,
                        execution_count,
                        events: notebook_events_ok(request.silent, "ok".to_string()),
                    });
                }
                Err(diagnostics) => {
                    self.sessions.insert(request.session, state);
                    return Ok(ExecuteReply {
                        status: ExecutionStatus::Error,
                        execution_count,
                        events: notebook_events_error(request.silent, &diagnostics),
                    });
                }
            }
        }

        let typed = match &state.typed {
            Some(typed) => typed.clone(),
            None => {
                let source = render_session_source(request.session, &state.snippets);
                match self.compile_checked_source(&source) {
                    Ok((_parsed, typed)) => typed,
                    Err(diagnostics) => {
                        self.sessions.insert(request.session, state);
                        return Ok(ExecuteReply {
                            status: ExecutionStatus::Error,
                            execution_count,
                            events: notebook_events_error(request.silent, &diagnostics),
                        });
                    }
                }
            }
        };

        let expr = match self.syntax.parse_expr(trimmed) {
            Ok(expr) => expr,
            Err(err) => {
                let diagnostics = err.into_diagnostics();
                self.sessions.insert(request.session, state);
                return Ok(ExecuteReply {
                    status: ExecutionStatus::Error,
                    execution_count,
                    events: notebook_events_error(request.silent, &diagnostics),
                });
            }
        };

        let reply = match self.semantics.evaluate_term(&typed, &expr) {
            Ok(outcome) => ExecuteReply {
                status: ExecutionStatus::Ok,
                execution_count,
                events: notebook_events_ok(request.silent, outcome.value),
            },
            Err(err) => {
                let diagnostics = err.into_diagnostics();
                ExecuteReply {
                    status: ExecutionStatus::Error,
                    execution_count,
                    events: notebook_events_error(request.silent, &diagnostics),
                }
            }
        };
        self.sessions.insert(request.session, state);
        Ok(reply)
    }

    fn complete(&self, code: &str, cursor: usize) -> Result<CompletionReply, LanguageError> {
        let cursor = cursor.min(code.len());
        let (start, end, prefix) = token_prefix_at_cursor(code, cursor);
        let mut candidates = BTreeSet::new();
        for keyword in BASE_COMPLETIONS {
            candidates.insert((*keyword).to_string());
        }
        candidates.extend(identifiers_in_text(code));
        let matches = candidates
            .into_iter()
            .filter(|item| item.starts_with(prefix.as_str()))
            .collect::<Vec<_>>();

        Ok(CompletionReply {
            matches,
            cursor_start: start,
            cursor_end: end,
        })
    }

    fn inspect(&self, code: &str, cursor: usize) -> Result<InspectReply, LanguageError> {
        let cursor = cursor.min(code.len());
        let (start, end, token) = token_prefix_at_cursor(code, cursor);
        if token.is_empty() {
            return Ok(InspectReply {
                found: false,
                contents: String::new(),
                cursor_start: start,
                cursor_end: end,
            });
        }

        Ok(InspectReply {
            found: true,
            contents: format!("symbol {}", token),
            cursor_start: start,
            cursor_end: end,
        })
    }

    fn interrupt(&mut self, session: SessionId) -> Result<(), LanguageError> {
        self.sessions.entry(session).or_default().interrupted = true;
        Ok(())
    }

    fn restart(&mut self, session: SessionId) -> Result<(), LanguageError> {
        self.sessions.insert(session, SessionState::default());
        Ok(())
    }

    fn shutdown(&mut self) -> Result<(), LanguageError> {
        self.kernel_shutdown = true;
        self.sessions.clear();
        Ok(())
    }
}

impl LanguageServer for ToolingEngine {
    fn open_document(&mut self, uri: &DocumentUri, text: &str) -> Result<(), LanguageError> {
        validate_lsp_uri(uri)?;
        self.documents.insert(
            uri.0.clone(),
            DocumentState {
                text: text.to_string(),
                saved: false,
            },
        );
        Ok(())
    }

    fn change_document(&mut self, uri: &DocumentUri, text: &str) -> Result<(), LanguageError> {
        validate_lsp_uri(uri)?;
        self.documents
            .entry(uri.0.clone())
            .and_modify(|doc| {
                doc.text = text.to_string();
                doc.saved = false;
            })
            .or_insert_with(|| DocumentState {
                text: text.to_string(),
                saved: false,
            });
        Ok(())
    }

    fn save_document(&mut self, uri: &DocumentUri) -> Result<(), LanguageError> {
        if let Some(doc) = self.documents.get_mut(&uri.0) {
            doc.saved = true;
        }
        Ok(())
    }

    fn close_document(&mut self, uri: &DocumentUri) -> Result<(), LanguageError> {
        self.documents.remove(&uri.0);
        Ok(())
    }

    fn diagnostics(&self, uri: &DocumentUri) -> Result<DiagnosticBundle, LanguageError> {
        let Some(doc) = self.documents.get(&uri.0) else {
            return Ok(DiagnosticBundle::default());
        };
        Ok(match self.compile_checked_source(&doc.text) {
            Ok(_) => DiagnosticBundle::default(),
            Err(bundle) => bundle,
        })
    }

    fn hover(
        &self,
        uri: &DocumentUri,
        position: Position,
    ) -> Result<Option<HoverReply>, LanguageError> {
        let Some(doc) = self.documents.get(&uri.0) else {
            return Ok(None);
        };
        let Some((token, start, end)) = token_at_position(&doc.text, position) else {
            return Ok(None);
        };
        Ok(Some(HoverReply {
            contents: format!("symbol {}", token),
            range: Some((start, end)),
        }))
    }

    fn definition(
        &self,
        uri: &DocumentUri,
        position: Position,
    ) -> Result<Option<DefinitionLocation>, LanguageError> {
        let Some(doc) = self.documents.get(&uri.0) else {
            return Ok(None);
        };
        let token = token_at_position(&doc.text, position)
            .map(|(raw, _, _)| raw)
            .unwrap_or_default();
        let target = token.rsplit('.').next().unwrap_or_default();
        let declarations = declaration_spans(&doc.text);
        if declarations.is_empty() {
            return Ok(None);
        }

        for (name, line, start, end) in &declarations {
            if name == target {
                return Ok(Some(DefinitionLocation {
                    uri: uri.clone(),
                    range: (
                        Position {
                            line: *line as u32,
                            character: *start as u32,
                        },
                        Position {
                            line: *line as u32,
                            character: *end as u32,
                        },
                    ),
                }));
            }
        }

        let (_name, line, start, end) = declarations[0].clone();
        Ok(Some(DefinitionLocation {
            uri: uri.clone(),
            range: (
                Position {
                    line: line as u32,
                    character: start as u32,
                },
                Position {
                    line: line as u32,
                    character: end as u32,
                },
            ),
        }))
    }

    fn completions(
        &self,
        uri: &DocumentUri,
        position: Position,
    ) -> Result<Vec<CompletionItem>, LanguageError> {
        let Some(doc) = self.documents.get(&uri.0) else {
            return Ok(Vec::new());
        };
        let mut candidates = BTreeSet::new();
        for item in BASE_COMPLETIONS {
            candidates.insert((*item).to_string());
        }
        for (name, ..) in declaration_spans(&doc.text) {
            candidates.insert(name);
        }
        candidates.extend(identifiers_in_text(&doc.text));

        let prefix = token_prefix_for_position(&doc.text, position);
        let completions = candidates
            .into_iter()
            .filter(|item| prefix.is_empty() || item.starts_with(prefix.as_str()))
            .map(|label| CompletionItem {
                detail: "symbol".to_string(),
                label,
            })
            .collect::<Vec<_>>();
        Ok(completions)
    }

    fn rename_symbol(
        &mut self,
        uri: &DocumentUri,
        position: Position,
        new_name: &str,
    ) -> Result<WorkspaceEdit, LanguageError> {
        let Some(doc) = self.documents.get(&uri.0) else {
            return Ok(WorkspaceEdit::default());
        };
        let token = token_at_position(&doc.text, position)
            .map(|(raw, _, _)| raw)
            .unwrap_or_default();
        let mut edits = rename_edits(&doc.text, &token, new_name);
        if edits.is_empty() {
            edits.push(TextEdit {
                range: (position, position),
                new_text: new_name.to_string(),
            });
        }
        Ok(WorkspaceEdit {
            changes: vec![(uri.clone(), edits)],
        })
    }

    fn semantic_tokens(&self, uri: &DocumentUri) -> Result<Vec<SemanticToken>, LanguageError> {
        let Some(doc) = self.documents.get(&uri.0) else {
            return Ok(Vec::new());
        };
        Ok(tokenize_semantic(&doc.text))
    }

    fn cancel(&mut self, request_id: RequestId) -> Result<(), LanguageError> {
        self.cancelled_requests.insert(request_id);
        Ok(())
    }
}

impl ToolingEngine {
    fn compile_checked_source(
        &self,
        source: &str,
    ) -> Result<(SurfaceModule, TypedModule), DiagnosticBundle> {
        let parsed = self
            .syntax
            .parse_module(source)
            .map_err(|err| err.into_diagnostics())?;
        let typed = self
            .semantics
            .elaborate_module(&parsed)
            .map_err(|err| err.into_diagnostics())?;
        Ok((parsed, typed))
    }

    fn invoke_check(&self, invocation: &CliInvocation) -> Result<CliResponse, LanguageError> {
        let json_mode = invocation.args.iter().any(|arg| arg == "--json");
        for arg in invocation.args.iter().skip(1) {
            if arg == "--unsafe-eval" {
                return Err(cli_error(
                    "unsafe option '--unsafe-eval' is forbidden".to_string(),
                ));
            }
            if arg != "--json" {
                return Ok(cli_error_response(
                    json_mode,
                    format!("unknown option '{}'", arg),
                    diagnostic(
                        "Cli",
                        "unknown_option",
                        format!("unknown option '{}'", arg),
                        None,
                    ),
                ));
            }
        }

        match self.compile_checked_source(&invocation.stdin) {
            Ok(_) => Ok(cli_ok_response(
                json_mode,
                String::new(),
                String::new(),
                DiagnosticBundle::default(),
                None,
            )),
            Err(diagnostics) => Ok(cli_error_response_from_bundle(json_mode, diagnostics, None)),
        }
    }

    fn invoke_build(&self, invocation: &CliInvocation) -> Result<CliResponse, LanguageError> {
        let json_mode = invocation.args.iter().any(|arg| arg == "--json");
        for arg in invocation.args.iter().skip(1) {
            if arg != "--json" {
                return Ok(cli_error_response(
                    json_mode,
                    format!("unknown option '{}'", arg),
                    diagnostic(
                        "Cli",
                        "unknown_option",
                        format!("unknown option '{}'", arg),
                        None,
                    ),
                ));
            }
        }

        match self.compile_checked_source(&invocation.stdin) {
            Ok(_) => Ok(cli_ok_response(
                json_mode,
                if json_mode {
                    String::new()
                } else {
                    "build succeeded\n".to_string()
                },
                String::new(),
                DiagnosticBundle::default(),
                None,
            )),
            Err(diagnostics) => Ok(cli_error_response_from_bundle(json_mode, diagnostics, None)),
        }
    }

    fn invoke_fmt(&self, invocation: &CliInvocation) -> Result<CliResponse, LanguageError> {
        let json_mode = invocation.args.iter().any(|arg| arg == "--json");
        let check_mode = invocation.args.iter().any(|arg| arg == "--check");
        for arg in invocation.args.iter().skip(1) {
            if arg != "--json" && arg != "--check" {
                return Ok(cli_error_response(
                    json_mode,
                    format!("unknown option '{}'", arg),
                    diagnostic(
                        "Cli",
                        "unknown_option",
                        format!("unknown option '{}'", arg),
                        None,
                    ),
                ));
            }
        }

        let (parsed, _) = match self.compile_checked_source(&invocation.stdin) {
            Ok(pair) => pair,
            Err(diagnostics) => {
                return Ok(cli_error_response_from_bundle(json_mode, diagnostics, None));
            }
        };

        let formatted = self
            .syntax
            .format_module(&parsed)
            .map_err(|err| cli_error(format_diagnostics(&err.into_diagnostics())))?;
        let normalized_in = normalize_newlines(&invocation.stdin).trim().to_string();
        let normalized_fmt = normalize_newlines(&formatted).trim().to_string();
        let matches = normalized_in == normalized_fmt;

        if check_mode && !matches {
            return Ok(cli_error_response(
                json_mode,
                "format check failed".to_string(),
                diagnostic(
                    "Format",
                    "format_check_failed",
                    "format check failed".to_string(),
                    None,
                ),
            ));
        }

        let stdout = if check_mode {
            String::new()
        } else {
            formatted.clone()
        };
        let extra = Some(vec![("formatted", formatted)]);
        Ok(cli_ok_response(
            json_mode,
            stdout,
            String::new(),
            DiagnosticBundle::default(),
            extra,
        ))
    }

    fn invoke_run(&self, invocation: &CliInvocation) -> Result<CliResponse, LanguageError> {
        let mut json_mode = false;
        let mut entry: Option<String> = None;
        let mut normalize: Option<String> = None;

        let mut index = 1usize;
        while index < invocation.args.len() {
            match invocation.args[index].as_str() {
                "--json" => {
                    json_mode = true;
                    index += 1;
                }
                "--entry" => {
                    let Some(value) = invocation.args.get(index + 1) else {
                        return Ok(cli_error_response(
                            json_mode,
                            "missing value for --entry".to_string(),
                            diagnostic(
                                "Cli",
                                "missing_option_value",
                                "missing value for --entry".to_string(),
                                None,
                            ),
                        ));
                    };
                    entry = Some(value.clone());
                    index += 2;
                }
                "--normalize" => {
                    let Some(value) = invocation.args.get(index + 1) else {
                        return Ok(cli_error_response(
                            json_mode,
                            "missing value for --normalize".to_string(),
                            diagnostic(
                                "Cli",
                                "missing_option_value",
                                "missing value for --normalize".to_string(),
                                None,
                            ),
                        ));
                    };
                    normalize = Some(value.clone());
                    index += 2;
                }
                other => {
                    return Ok(cli_error_response(
                        json_mode,
                        format!("unknown option '{}'", other),
                        diagnostic(
                            "Cli",
                            "unknown_option",
                            format!("unknown option '{}'", other),
                            None,
                        ),
                    ));
                }
            }
        }

        if entry.is_none() && normalize.is_none() {
            return Ok(cli_error_response(
                json_mode,
                "run requires exactly one of --entry or --normalize".to_string(),
                diagnostic(
                    "Cli",
                    "missing_selector",
                    "run requires exactly one of --entry or --normalize".to_string(),
                    None,
                ),
            ));
        }
        if entry.is_some() && normalize.is_some() {
            return Ok(cli_error_response(
                json_mode,
                "run selectors --entry and --normalize are mutually exclusive".to_string(),
                diagnostic(
                    "Cli",
                    "conflicting_selectors",
                    "run selectors --entry and --normalize are mutually exclusive".to_string(),
                    None,
                ),
            ));
        }

        let (_parsed, typed) = match self.compile_checked_source(&invocation.stdin) {
            Ok(pair) => pair,
            Err(diagnostics) => {
                return Ok(cli_error_response_from_bundle(json_mode, diagnostics, None));
            }
        };

        if let Some(entry_name) = entry {
            let term = entry_name
                .rsplit('.')
                .next()
                .map(str::to_string)
                .unwrap_or(entry_name.clone());
            let expr = Expr::var(term);
            return match self.semantics.evaluate_term(&typed, &expr) {
                Ok(value) => {
                    let stdout = format!("{}\n", value.value);
                    Ok(cli_ok_response(
                        json_mode,
                        stdout,
                        String::new(),
                        DiagnosticBundle::default(),
                        Some(vec![("value", value.value)]),
                    ))
                }
                Err(err) => Ok(cli_error_response_from_bundle(
                    json_mode,
                    err.into_diagnostics(),
                    None,
                )),
            };
        }

        let normalize_name = normalize.unwrap_or_default();
        let expr = Expr::var(
            normalize_name
                .rsplit('.')
                .next()
                .map(str::to_string)
                .unwrap_or(normalize_name),
        );
        match self.semantics.normalize_term(&typed, &expr) {
            Ok(normal_form) => {
                let rendered = normal_form.structure().to_string();
                let stdout = format!("{}\n", rendered);
                Ok(cli_ok_response(
                    json_mode,
                    stdout,
                    String::new(),
                    DiagnosticBundle::default(),
                    Some(vec![("normal_form", rendered)]),
                ))
            }
            Err(err) => Ok(cli_error_response_from_bundle(
                json_mode,
                err.into_diagnostics(),
                None,
            )),
        }
    }

    fn invoke_repl(&self, invocation: &CliInvocation) -> Result<CliResponse, LanguageError> {
        let json_mode = invocation.args.iter().any(|arg| arg == "--json");
        for arg in invocation.args.iter().skip(1) {
            if arg != "--json" {
                return Ok(cli_error_response(
                    json_mode,
                    format!("unknown option '{}'", arg),
                    diagnostic(
                        "Cli",
                        "unknown_option",
                        format!("unknown option '{}'", arg),
                        None,
                    ),
                ));
            }
        }

        Ok(cli_ok_response(
            json_mode,
            String::new(),
            String::new(),
            DiagnosticBundle::default(),
            Some(vec![("mode", "repl".to_string())]),
        ))
    }

    fn invoke_lsp(&self, invocation: &CliInvocation) -> Result<CliResponse, LanguageError> {
        let json_mode = invocation.args.iter().any(|arg| arg == "--json");
        for arg in invocation.args.iter().skip(1) {
            if arg != "--json" && arg != "--stdio" {
                return Ok(cli_error_response(
                    json_mode,
                    format!("unknown option '{}'", arg),
                    diagnostic(
                        "Cli",
                        "unknown_option",
                        format!("unknown option '{}'", arg),
                        None,
                    ),
                ));
            }
        }
        Ok(cli_ok_response(
            json_mode,
            String::new(),
            String::new(),
            DiagnosticBundle::default(),
            Some(vec![("mode", "lsp".to_string())]),
        ))
    }

    fn invoke_notebook(&self, invocation: &CliInvocation) -> Result<CliResponse, LanguageError> {
        let json_mode = invocation.args.iter().any(|arg| arg == "--json");
        if invocation.args.len() < 2 || invocation.args[1] != "kernel" {
            return Ok(cli_error_response(
                json_mode,
                "notebook requires `kernel` subcommand".to_string(),
                diagnostic(
                    "Cli",
                    "missing_subcommand",
                    "notebook requires `kernel` subcommand".to_string(),
                    None,
                ),
            ));
        }
        for arg in invocation.args.iter().skip(2) {
            if arg != "--json" {
                return Ok(cli_error_response(
                    json_mode,
                    format!("unknown option '{}'", arg),
                    diagnostic(
                        "Cli",
                        "unknown_option",
                        format!("unknown option '{}'", arg),
                        None,
                    ),
                ));
            }
        }
        let info = self.kernel_info()?;
        Ok(cli_ok_response(
            json_mode,
            String::new(),
            String::new(),
            DiagnosticBundle::default(),
            Some(vec![
                ("language_name", info.language_name),
                ("file_extension", info.file_extension),
            ]),
        ))
    }
}

#[derive(Debug, Clone, Copy)]
enum ReplPhase {
    Submit,
    Complete,
    End,
}

#[derive(Debug, Clone, Copy)]
enum NotebookPhase {
    Execute,
    KernelInfo,
    Complete,
    Inspect,
    Interrupt,
    Restart,
    Shutdown,
}

fn module_error_from_bundle(err: LanguageError) -> LanguageError {
    LanguageError::ModuleSystem(ModuleSystemError::BuildGraph {
        diagnostics: err.into_diagnostics(),
    })
}

fn module_system_error(code: &str, message: String) -> LanguageError {
    LanguageError::ModuleSystem(ModuleSystemError::BuildGraph {
        diagnostics: DiagnosticBundle {
            diagnostics: vec![diagnostic("ModuleSystem", code, message, None)],
        },
    })
}

fn cli_error(message: String) -> LanguageError {
    LanguageError::Interaction(InteractionError::CliInvoke {
        diagnostics: DiagnosticBundle {
            diagnostics: vec![diagnostic("Cli", "invoke_error", message, None)],
        },
    })
}

fn repl_error(message: String, phase: ReplPhase) -> LanguageError {
    let diagnostics = DiagnosticBundle {
        diagnostics: vec![diagnostic("Repl", "session_error", message, None)],
    };
    let variant = match phase {
        ReplPhase::Submit => ReplError::Submit { diagnostics },
        ReplPhase::Complete => ReplError::Complete { diagnostics },
        ReplPhase::End => ReplError::End { diagnostics },
    };
    LanguageError::Interaction(InteractionError::Repl(variant))
}

fn notebook_error(message: String, phase: NotebookPhase) -> LanguageError {
    let diagnostics = DiagnosticBundle {
        diagnostics: vec![diagnostic("Notebook", "protocol_error", message, None)],
    };
    let variant = match phase {
        NotebookPhase::Execute => NotebookError::Execute { diagnostics },
        NotebookPhase::KernelInfo => NotebookError::KernelInfo { diagnostics },
        NotebookPhase::Complete => NotebookError::Complete { diagnostics },
        NotebookPhase::Inspect => NotebookError::Inspect { diagnostics },
        NotebookPhase::Interrupt => NotebookError::Interrupt { diagnostics },
        NotebookPhase::Restart => NotebookError::Restart { diagnostics },
        NotebookPhase::Shutdown => NotebookError::Shutdown { diagnostics },
    };
    LanguageError::Interaction(InteractionError::Notebook(variant))
}

fn lsp_error(message: String, phase: fn(DiagnosticBundle) -> LspError) -> LanguageError {
    let diagnostics = DiagnosticBundle {
        diagnostics: vec![diagnostic("Lsp", "protocol_error", message, None)],
    };
    LanguageError::Interaction(InteractionError::Lsp(phase(diagnostics)))
}

fn diagnostic(category: &str, code: &str, message: String, span: Option<Span>) -> Diagnostic {
    Diagnostic {
        code: code.to_string(),
        category: category.to_string(),
        severity: Severity::Error,
        message,
        span,
        source: None,
    }
}

fn cli_ok_response(
    json_mode: bool,
    stdout: String,
    stderr: String,
    diagnostics: DiagnosticBundle,
    extra_fields: Option<Vec<(&str, String)>>,
) -> CliResponse {
    let json = if json_mode {
        Some(json_payload(
            "ok",
            &diagnostics,
            extra_fields.unwrap_or_default(),
        ))
    } else {
        None
    };
    CliResponse {
        exit_code: 0,
        stdout,
        stderr,
        json,
    }
}

fn cli_error_response(
    json_mode: bool,
    stderr_message: impl Into<String>,
    diag: Diagnostic,
) -> CliResponse {
    let diagnostics = DiagnosticBundle {
        diagnostics: vec![diag],
    };
    cli_error_response_from_bundle(json_mode, diagnostics, Some(stderr_message.into()))
}

fn cli_error_response_from_bundle(
    json_mode: bool,
    diagnostics: DiagnosticBundle,
    stderr_override: Option<String>,
) -> CliResponse {
    let stderr = stderr_override.unwrap_or_else(|| format_diagnostics(&diagnostics));
    let json = if json_mode {
        Some(json_payload("error", &diagnostics, Vec::new()))
    } else {
        None
    };
    CliResponse {
        exit_code: 1,
        stdout: String::new(),
        stderr,
        json,
    }
}

fn format_diagnostics(bundle: &DiagnosticBundle) -> String {
    if bundle.diagnostics.is_empty() {
        return String::new();
    }
    let mut out = String::new();
    for diag in &bundle.diagnostics {
        out.push_str(&format!("[{}] {}\n", diag.category, diag.message));
    }
    out
}

fn json_payload(
    status: &str,
    diagnostics: &DiagnosticBundle,
    extra_fields: Vec<(&str, String)>,
) -> String {
    let mut fields = Vec::new();
    fields.push(format!("\"status\":\"{}\"", escape_json(status)));
    for (key, value) in extra_fields {
        fields.push(format!(
            "\"{}\":\"{}\"",
            escape_json(key),
            escape_json(&value)
        ));
    }
    fields.push(format!("\"diagnostics\":{}", diagnostics_json(diagnostics)));
    format!("{{{}}}", fields.join(","))
}

fn diagnostics_json(bundle: &DiagnosticBundle) -> String {
    let entries = bundle
        .diagnostics
        .iter()
        .map(diagnostic_json)
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(","))
}

fn diagnostic_json(diagnostic: &Diagnostic) -> String {
    let span = match diagnostic.span {
        Some(span) => format!("{{\"start\":{},\"end\":{}}}", span.start, span.end),
        None => "null".to_string(),
    };
    let source = diagnostic
        .source
        .as_ref()
        .map(|s| format!("\"{}\"", escape_json(s)))
        .unwrap_or_else(|| "null".to_string());
    format!(
        "{{\"code\":\"{}\",\"category\":\"{}\",\"severity\":\"{}\",\"message\":\"{}\",\"span\":{},\"source\":{}}}",
        escape_json(&diagnostic.code),
        escape_json(&diagnostic.category),
        severity_label(diagnostic.severity),
        escape_json(&diagnostic.message),
        span,
        source
    )
}

fn severity_label(severity: Severity) -> &'static str {
    match severity {
        Severity::Error => "Error",
        Severity::Warning => "Warning",
        Severity::Info => "Info",
    }
}

fn escape_json(value: &str) -> String {
    let mut out = String::new();
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

fn is_full_module_source(text: &str) -> bool {
    text.trim_start().starts_with("module ")
}

fn looks_like_declaration(text: &str) -> bool {
    let trimmed = text.trim();
    trimmed.starts_with("postulate ")
        || trimmed.contains(" : ")
        || trimmed.contains(':')
        || trimmed.contains('=')
}

fn render_session_source(session: SessionId, snippets: &[String]) -> String {
    let mut source = format!("module ReplSession{} where\n", session);
    for snippet in snippets {
        source.push_str(snippet);
        if !snippet.ends_with('\n') {
            source.push('\n');
        }
    }
    source
}

fn source_with_appended_snippet(session: SessionId, snippets: &[String], snippet: &str) -> String {
    let mut source = render_session_source(session, snippets);
    source.push_str(snippet);
    if !snippet.ends_with('\n') {
        source.push('\n');
    }
    source
}

fn notebook_events_ok(silent: bool, rendered: String) -> Vec<NotebookEvent> {
    if silent {
        return Vec::new();
    }
    vec![NotebookEvent::ExecuteResult { repr: rendered }]
}

fn notebook_events_error(silent: bool, diagnostics: &DiagnosticBundle) -> Vec<NotebookEvent> {
    if silent {
        return Vec::new();
    }
    diagnostics
        .diagnostics
        .iter()
        .map(|diag| NotebookEvent::Error {
            ename: diag.category.clone(),
            evalue: diag.message.clone(),
        })
        .collect::<Vec<_>>()
}

fn contains_unsafe_primitive(code: &str) -> bool {
    let lowered = code.to_ascii_lowercase();
    lowered.contains("open(")
        || lowered.contains("net.connect")
        || lowered.contains("std::fs")
        || lowered.contains("socket")
        || lowered.contains("http://")
        || lowered.contains("https://")
}

fn validate_lsp_uri(uri: &DocumentUri) -> Result<(), LanguageError> {
    if uri.0.contains("/../") || uri.0.contains("\\..\\") || uri.0.contains("..\\") {
        return Err(lsp_error(
            "uri traversal is not allowed".to_string(),
            |diagnostics| LspError::OpenDocument { diagnostics },
        ));
    }
    Ok(())
}

fn token_prefix_at_cursor(text: &str, cursor: usize) -> (usize, usize, String) {
    let bytes = text.as_bytes();
    let mut start = cursor.min(bytes.len());
    while start > 0 {
        let c = bytes[start - 1] as char;
        if is_ident_char(c) {
            start -= 1;
        } else {
            break;
        }
    }
    let mut end = cursor.min(bytes.len());
    while end < bytes.len() {
        let c = bytes[end] as char;
        if is_ident_char(c) {
            end += 1;
        } else {
            break;
        }
    }
    let token = text[start..cursor.min(end)].to_string();
    (start, cursor.min(bytes.len()), token)
}

fn token_at_position(text: &str, position: Position) -> Option<(String, Position, Position)> {
    let line_idx = position.line as usize;
    let line = text.lines().nth(line_idx)?;
    if line.is_empty() {
        return None;
    }
    let chars = line.chars().collect::<Vec<_>>();
    let mut cursor = position.character as usize;
    if cursor >= chars.len() {
        cursor = chars.len().saturating_sub(1);
    }
    if !is_ident_char(chars[cursor]) {
        if cursor > 0 && is_ident_char(chars[cursor - 1]) {
            cursor -= 1;
        } else {
            return None;
        }
    }
    let mut start = cursor;
    while start > 0 && is_ident_char(chars[start - 1]) {
        start -= 1;
    }
    let mut end = cursor;
    while end + 1 < chars.len() && is_ident_char(chars[end + 1]) {
        end += 1;
    }
    let token = chars[start..=end].iter().collect::<String>();
    Some((
        token,
        Position {
            line: position.line,
            character: start as u32,
        },
        Position {
            line: position.line,
            character: (end + 1) as u32,
        },
    ))
}

fn token_prefix_for_position(text: &str, position: Position) -> String {
    let line_idx = position.line as usize;
    let Some(line) = text.lines().nth(line_idx) else {
        return String::new();
    };
    if line.is_empty() {
        return String::new();
    }
    let chars = line.chars().collect::<Vec<_>>();
    let mut cursor = (position.character as usize).min(chars.len());
    while cursor > 0 && !is_ident_char(chars[cursor - 1]) {
        if cursor == 0 {
            break;
        }
        cursor -= 1;
    }
    let mut start = cursor;
    while start > 0 && is_ident_char(chars[start - 1]) {
        start -= 1;
    }
    chars[start..cursor].iter().collect::<String>()
}

fn declaration_spans(text: &str) -> Vec<(String, usize, usize, usize)> {
    let mut out = Vec::new();
    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim_start();
        let offset = line.len().saturating_sub(trimmed.len());
        if let Some(rest) = trimmed.strip_prefix("postulate ") {
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':' || c == '(')
                .next()
                .unwrap_or_default();
            if !name.is_empty() {
                let start = offset + "postulate ".len();
                out.push((name.to_string(), line_idx, start, start + name.len()));
            }
            continue;
        }

        if let Some(colon_idx) = find_top_level_char(trimmed, ':') {
            let lhs = trimmed[..colon_idx].trim();
            let name = lhs
                .split(|c: char| c.is_whitespace() || c == '(')
                .next()
                .unwrap_or_default();
            if !name.is_empty()
                && name != "module"
                && name != "import"
                && name != "where"
                && let Some(local_start) = line.find(name)
            {
                out.push((
                    name.to_string(),
                    line_idx,
                    local_start,
                    local_start + name.len(),
                ));
            }
        }
    }
    out
}

fn find_top_level_char(text: &str, target: char) -> Option<usize> {
    let mut paren = 0i32;
    let mut brace = 0i32;
    let mut bracket = 0i32;
    for (idx, ch) in text.char_indices() {
        match ch {
            '(' => paren += 1,
            ')' => paren -= 1,
            '{' => brace += 1,
            '}' => brace -= 1,
            '[' => bracket += 1,
            ']' => bracket -= 1,
            _ => {}
        }
        if ch == target && paren == 0 && brace == 0 && bracket == 0 {
            return Some(idx);
        }
    }
    None
}

fn rename_edits(text: &str, old: &str, new_name: &str) -> Vec<TextEdit> {
    if old.is_empty() {
        return Vec::new();
    }
    let mut edits = Vec::new();
    for (line_idx, line) in text.lines().enumerate() {
        let chars = line.chars().collect::<Vec<_>>();
        let mut start = 0usize;
        while start < chars.len() {
            if !is_ident_char(chars[start]) {
                start += 1;
                continue;
            }
            let mut end = start + 1;
            while end < chars.len() && is_ident_char(chars[end]) {
                end += 1;
            }
            let token = chars[start..end].iter().collect::<String>();
            if token == old {
                edits.push(TextEdit {
                    range: (
                        Position {
                            line: line_idx as u32,
                            character: start as u32,
                        },
                        Position {
                            line: line_idx as u32,
                            character: end as u32,
                        },
                    ),
                    new_text: new_name.to_string(),
                });
            }
            start = end;
        }
    }
    edits
}

fn tokenize_semantic(text: &str) -> Vec<SemanticToken> {
    let mut tokens = Vec::new();
    for (line_idx, line) in text.lines().enumerate() {
        let chars = line.chars().collect::<Vec<_>>();
        let mut cursor = 0usize;
        while cursor < chars.len() {
            if chars[cursor].is_whitespace() {
                cursor += 1;
                continue;
            }
            if chars[cursor] == '-' && cursor + 1 < chars.len() && chars[cursor + 1] == '-' {
                let length = chars.len() - cursor;
                tokens.push(SemanticToken {
                    line: line_idx as u32,
                    start_character: cursor as u32,
                    length: length as u32,
                    token_type: SemanticTokenType::Comment,
                    modifiers: Vec::new(),
                });
                break;
            }

            if is_ident_char(chars[cursor]) {
                let start = cursor;
                cursor += 1;
                while cursor < chars.len() && is_ident_char(chars[cursor]) {
                    cursor += 1;
                }
                let raw = chars[start..cursor].iter().collect::<String>();
                let token_type = if is_keyword(&raw) {
                    SemanticTokenType::Keyword
                } else if raw == "Cat" || raw == "Prop" || raw == "Top" {
                    SemanticTokenType::Type
                } else if raw.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                    SemanticTokenType::Module
                } else {
                    SemanticTokenType::Variable
                };
                tokens.push(SemanticToken {
                    line: line_idx as u32,
                    start_character: start as u32,
                    length: (cursor - start) as u32,
                    token_type,
                    modifiers: Vec::new(),
                });
                continue;
            }

            tokens.push(SemanticToken {
                line: line_idx as u32,
                start_character: cursor as u32,
                length: 1,
                token_type: SemanticTokenType::Operator,
                modifiers: Vec::new(),
            });
            cursor += 1;
        }
    }
    tokens
}

fn identifiers_in_text(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for line in text.lines() {
        let chars = line.chars().collect::<Vec<_>>();
        let mut cursor = 0usize;
        while cursor < chars.len() {
            if !is_ident_char(chars[cursor]) {
                cursor += 1;
                continue;
            }
            let start = cursor;
            cursor += 1;
            while cursor < chars.len() && is_ident_char(chars[cursor]) {
                cursor += 1;
            }
            let token = chars[start..cursor].iter().collect::<String>();
            if token
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic())
            {
                out.insert(token);
            }
        }
    }
    out
}

fn is_ident_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_' || ch == '.'
}

fn is_keyword(token: &str) -> bool {
    matches!(
        token,
        "module"
            | "where"
            | "import"
            | "postulate"
            | "as"
            | "using"
            | "hiding"
            | "renaming"
            | "let"
            | "in"
            | "refl"
            | "J"
            | "end"
            | "coend"
    )
}

fn normalize_newlines(text: &str) -> String {
    text.replace("\r\n", "\n")
}
