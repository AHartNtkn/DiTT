use std::collections::BTreeMap;
use std::fmt;

use super::foundation::DiagnosticBundle;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CliInvocation {
    pub args: Vec<String>,
    pub stdin: String,
    pub env: BTreeMap<String, String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CliResponse {
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
    pub json: Option<String>,
}

pub type SessionId = u64;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplOutput {
    pub rendered: String,
    pub diagnostics: DiagnosticBundle,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelInfo {
    pub language_name: String,
    pub language_version: String,
    pub mimetype: String,
    pub file_extension: String,
    pub banner: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecuteRequest {
    pub session: SessionId,
    pub code: String,
    pub silent: bool,
    pub store_history: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionReply {
    pub matches: Vec<String>,
    pub cursor_start: usize,
    pub cursor_end: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NotebookEvent {
    Stream { name: String, text: String },
    // Jupyter protocol adaptation: mime mirrors display_data content-type keys.
    DisplayData { mime: String, data: String },
    ExecuteResult { repr: String },
    Error { ename: String, evalue: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecutionStatus {
    Ok,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecuteReply {
    pub status: ExecutionStatus,
    pub execution_count: u64,
    pub events: Vec<NotebookEvent>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InspectReply {
    pub found: bool,
    pub contents: String,
    pub cursor_start: usize,
    pub cursor_end: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticToken {
    pub line: u32,
    pub start_character: u32,
    pub length: u32,
    pub token_type: SemanticTokenType,
    pub modifiers: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticTokenType {
    Keyword,
    Type,
    Variable,
    Operator,
    Literal,
    Comment,
    /// Paper's term/functor level.
    Function,
    /// Tooling-only; no paper equivalent.
    Module,
    /// Paper's predicate level (Figure 9 predicate forms).
    Predicate,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocumentUri(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RequestId {
    Number(i64),
    String(String),
}

impl From<i64> for RequestId {
    fn from(value: i64) -> Self {
        Self::Number(value)
    }
}

impl From<i32> for RequestId {
    fn from(value: i32) -> Self {
        Self::Number(i64::from(value))
    }
}

impl From<u64> for RequestId {
    fn from(value: u64) -> Self {
        match i64::try_from(value) {
            Ok(v) => Self::Number(v),
            Err(_) => Self::String(value.to_string()),
        }
    }
}

impl From<u32> for RequestId {
    fn from(value: u32) -> Self {
        Self::Number(i64::from(value))
    }
}

impl From<usize> for RequestId {
    fn from(value: usize) -> Self {
        match i64::try_from(value) {
            Ok(v) => Self::Number(v),
            Err(_) => Self::String(value.to_string()),
        }
    }
}

impl From<String> for RequestId {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<&str> for RequestId {
    fn from(value: &str) -> Self {
        Self::String(value.to_string())
    }
}

impl fmt::Display for RequestId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RequestId::Number(value) => write!(f, "{value}"),
            RequestId::String(value) => write!(f, "{value}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HoverReply {
    pub contents: String,
    pub range: Option<(Position, Position)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionLocation {
    pub uri: DocumentUri,
    pub range: (Position, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextEdit {
    pub range: (Position, Position),
    pub new_text: String,
}

/// LSP protocol adaptation: workspace edits follow the protocol's uri->text-edit mapping.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WorkspaceEdit {
    pub changes: Vec<(DocumentUri, Vec<TextEdit>)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionItem {
    pub label: String,
    pub detail: String,
}
