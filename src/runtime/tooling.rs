use crate::api::*;

#[derive(Debug, Default)]
pub struct ToolingEngine {
    _private: (),
}

impl ModuleSystem for ToolingEngine {
    fn build_graph(&self, _modules: &[ModuleText]) -> Result<ModuleGraph, LanguageError> {
        unimplemented!("module_system.build_graph")
    }
}

impl Cli for ToolingEngine {
    fn invoke(&self, _invocation: &CliInvocation) -> Result<CliResponse, LanguageError> {
        unimplemented!("cli.invoke")
    }
}

impl Repl for ToolingEngine {
    fn start_session(&mut self) -> Result<SessionId, LanguageError> {
        unimplemented!("repl.start_session")
    }

    fn submit(&mut self, _session: SessionId, _input: &str) -> Result<ReplOutput, LanguageError> {
        unimplemented!("repl.submit")
    }

    fn complete(&self, _session: SessionId, _prefix: &str) -> Result<Vec<String>, LanguageError> {
        unimplemented!("repl.complete")
    }

    fn end_session(&mut self, _session: SessionId) -> Result<(), LanguageError> {
        unimplemented!("repl.end_session")
    }
}

impl NotebookKernel for ToolingEngine {
    fn kernel_info(&self) -> Result<KernelInfo, LanguageError> {
        unimplemented!("notebook.kernel_info")
    }

    fn execute(&mut self, _request: &ExecuteRequest) -> Result<ExecuteReply, LanguageError> {
        unimplemented!("notebook.execute")
    }

    fn complete(&self, _code: &str, _cursor: usize) -> Result<CompletionReply, LanguageError> {
        unimplemented!("notebook.complete")
    }

    fn inspect(&self, _code: &str, _cursor: usize) -> Result<InspectReply, LanguageError> {
        unimplemented!("notebook.inspect")
    }

    fn interrupt(&mut self, _session: SessionId) -> Result<(), LanguageError> {
        unimplemented!("notebook.interrupt")
    }

    fn restart(&mut self, _session: SessionId) -> Result<(), LanguageError> {
        unimplemented!("notebook.restart")
    }

    fn shutdown(&mut self) -> Result<(), LanguageError> {
        unimplemented!("notebook.shutdown")
    }
}

impl LanguageServer for ToolingEngine {
    fn open_document(&mut self, _uri: &DocumentUri, _text: &str) -> Result<(), LanguageError> {
        unimplemented!("lsp.open_document")
    }

    fn change_document(&mut self, _uri: &DocumentUri, _text: &str) -> Result<(), LanguageError> {
        unimplemented!("lsp.change_document")
    }

    fn save_document(&mut self, _uri: &DocumentUri) -> Result<(), LanguageError> {
        unimplemented!("lsp.save_document")
    }

    fn close_document(&mut self, _uri: &DocumentUri) -> Result<(), LanguageError> {
        unimplemented!("lsp.close_document")
    }

    fn diagnostics(&self, _uri: &DocumentUri) -> Result<DiagnosticBundle, LanguageError> {
        unimplemented!("lsp.diagnostics")
    }

    fn hover(
        &self,
        _uri: &DocumentUri,
        _position: Position,
    ) -> Result<Option<HoverReply>, LanguageError> {
        unimplemented!("lsp.hover")
    }

    fn definition(
        &self,
        _uri: &DocumentUri,
        _position: Position,
    ) -> Result<Option<DefinitionLocation>, LanguageError> {
        unimplemented!("lsp.definition")
    }

    fn completions(
        &self,
        _uri: &DocumentUri,
        _position: Position,
    ) -> Result<Vec<CompletionItem>, LanguageError> {
        unimplemented!("lsp.completions")
    }

    fn rename_symbol(
        &mut self,
        _uri: &DocumentUri,
        _position: Position,
        _new_name: &str,
    ) -> Result<WorkspaceEdit, LanguageError> {
        unimplemented!("lsp.rename_symbol")
    }

    fn semantic_tokens(&self, _uri: &DocumentUri) -> Result<Vec<SemanticToken>, LanguageError> {
        unimplemented!("lsp.semantic_tokens")
    }

    fn cancel(&mut self, _request_id: RequestId) -> Result<(), LanguageError> {
        unimplemented!("lsp.cancel")
    }
}
