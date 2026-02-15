use super::*;

pub trait ModuleSystem {
    fn build_graph(&self, modules: &[ModuleText]) -> Result<ModuleGraph, LanguageError>;
}

pub trait Cli {
    fn invoke(&self, invocation: &CliInvocation) -> Result<CliResponse, LanguageError>;
}

pub trait Repl {
    fn start_session(&mut self) -> Result<SessionId, LanguageError>;
    fn submit(&mut self, session: SessionId, input: &str) -> Result<ReplOutput, LanguageError>;
    fn complete(&self, session: SessionId, prefix: &str) -> Result<Vec<String>, LanguageError>;
    fn end_session(&mut self, session: SessionId) -> Result<(), LanguageError>;
}

pub trait NotebookKernel {
    fn kernel_info(&self) -> Result<KernelInfo, LanguageError>;
    fn execute(&mut self, request: &ExecuteRequest) -> Result<ExecuteReply, LanguageError>;
    fn complete(&self, code: &str, cursor: usize) -> Result<CompletionReply, LanguageError>;
    fn inspect(&self, code: &str, cursor: usize) -> Result<InspectReply, LanguageError>;
    fn interrupt(&mut self, session: SessionId) -> Result<(), LanguageError>;
    fn restart(&mut self, session: SessionId) -> Result<(), LanguageError>;
    fn shutdown(&mut self) -> Result<(), LanguageError>;
}

pub trait LanguageServer {
    fn open_document(&mut self, uri: &DocumentUri, text: &str) -> Result<(), LanguageError>;
    fn change_document(&mut self, uri: &DocumentUri, text: &str) -> Result<(), LanguageError>;
    fn save_document(&mut self, uri: &DocumentUri) -> Result<(), LanguageError>;
    fn close_document(&mut self, uri: &DocumentUri) -> Result<(), LanguageError>;
    fn diagnostics(&self, uri: &DocumentUri) -> Result<DiagnosticBundle, LanguageError>;
    fn hover(
        &self,
        uri: &DocumentUri,
        position: Position,
    ) -> Result<Option<HoverReply>, LanguageError>;
    fn definition(
        &self,
        uri: &DocumentUri,
        position: Position,
    ) -> Result<Option<DefinitionLocation>, LanguageError>;
    fn completions(
        &self,
        uri: &DocumentUri,
        position: Position,
    ) -> Result<Vec<CompletionItem>, LanguageError>;
    fn rename_symbol(
        &mut self,
        uri: &DocumentUri,
        position: Position,
        new_name: &str,
    ) -> Result<WorkspaceEdit, LanguageError>;
    fn semantic_tokens(&self, uri: &DocumentUri) -> Result<Vec<SemanticToken>, LanguageError>;
    fn cancel(&mut self, request_id: RequestId) -> Result<(), LanguageError>;
}
