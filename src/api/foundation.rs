use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LanguageError {
    Syntax(SyntaxError),
    StaticSemantics(StaticSemanticsError),
    DynamicSemantics(DynamicSemanticsError),
    ModuleSystem(ModuleSystemError),
    Interaction(InteractionError),
    DerivationArtifact(DerivationArtifactError),
}

impl LanguageError {
    pub fn diagnostics(&self) -> &DiagnosticBundle {
        match self {
            LanguageError::Syntax(err) => err.diagnostics(),
            LanguageError::StaticSemantics(err) => err.diagnostics(),
            LanguageError::DynamicSemantics(err) => err.diagnostics(),
            LanguageError::ModuleSystem(err) => err.diagnostics(),
            LanguageError::Interaction(err) => err.diagnostics(),
            LanguageError::DerivationArtifact(err) => err.diagnostics(),
        }
    }

    pub fn into_diagnostics(self) -> DiagnosticBundle {
        match self {
            LanguageError::Syntax(err) => err.into_diagnostics(),
            LanguageError::StaticSemantics(err) => err.into_diagnostics(),
            LanguageError::DynamicSemantics(err) => err.into_diagnostics(),
            LanguageError::ModuleSystem(err) => err.into_diagnostics(),
            LanguageError::Interaction(err) => err.into_diagnostics(),
            LanguageError::DerivationArtifact(err) => err.into_diagnostics(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxError {
    Lex { diagnostics: DiagnosticBundle },
    Parse { diagnostics: DiagnosticBundle },
    ParseTerm { diagnostics: DiagnosticBundle },
    FormatModule { diagnostics: DiagnosticBundle },
    AlphaEquivalence { diagnostics: DiagnosticBundle },
}

macro_rules! impl_diagnostics {
    ($ty:ident { $($variant:ident),+ $(,)? }) => {
        impl $ty {
            pub fn diagnostics(&self) -> &DiagnosticBundle {
                match self {
                    $( $ty::$variant { diagnostics } )|+ => diagnostics,
                }
            }

            pub fn into_diagnostics(self) -> DiagnosticBundle {
                match self {
                    $( $ty::$variant { diagnostics } )|+ => diagnostics,
                }
            }
        }
    };
}

impl_diagnostics!(SyntaxError {
    Lex,
    Parse,
    ParseTerm,
    FormatModule,
    AlphaEquivalence
});

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StaticSemanticsError {
    ElaborateModule { diagnostics: DiagnosticBundle },
    InferType { diagnostics: DiagnosticBundle },
    DeriveJudgment { diagnostics: DiagnosticBundle },
    ComputeVariance { diagnostics: DiagnosticBundle },
    AllVariances { diagnostics: DiagnosticBundle },
}

impl_diagnostics!(StaticSemanticsError {
    ElaborateModule,
    InferType,
    DeriveJudgment,
    ComputeVariance,
    AllVariances
});

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DynamicSemanticsError {
    NormalizeTerm { diagnostics: DiagnosticBundle },
    DefinitionallyEqual { diagnostics: DiagnosticBundle },
    Evaluate { diagnostics: DiagnosticBundle },
}

impl_diagnostics!(DynamicSemanticsError {
    NormalizeTerm,
    DefinitionallyEqual,
    Evaluate
});

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleSystemError {
    BuildGraph { diagnostics: DiagnosticBundle },
}

impl_diagnostics!(ModuleSystemError { BuildGraph });

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InteractionError {
    CliInvoke { diagnostics: DiagnosticBundle },
    Repl(ReplError),
    Notebook(NotebookError),
    Lsp(LspError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReplError {
    Start { diagnostics: DiagnosticBundle },
    Submit { diagnostics: DiagnosticBundle },
    Complete { diagnostics: DiagnosticBundle },
    End { diagnostics: DiagnosticBundle },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NotebookError {
    KernelInfo { diagnostics: DiagnosticBundle },
    Execute { diagnostics: DiagnosticBundle },
    Complete { diagnostics: DiagnosticBundle },
    Inspect { diagnostics: DiagnosticBundle },
    Interrupt { diagnostics: DiagnosticBundle },
    Restart { diagnostics: DiagnosticBundle },
    Shutdown { diagnostics: DiagnosticBundle },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LspError {
    OpenDocument { diagnostics: DiagnosticBundle },
    ChangeDocument { diagnostics: DiagnosticBundle },
    SaveDocument { diagnostics: DiagnosticBundle },
    CloseDocument { diagnostics: DiagnosticBundle },
    Diagnostics { diagnostics: DiagnosticBundle },
    Hover { diagnostics: DiagnosticBundle },
    Definition { diagnostics: DiagnosticBundle },
    Completions { diagnostics: DiagnosticBundle },
    RenameSymbol { diagnostics: DiagnosticBundle },
    SemanticTokens { diagnostics: DiagnosticBundle },
    Cancel { diagnostics: DiagnosticBundle },
}

impl_diagnostics!(ReplError {
    Start,
    Submit,
    Complete,
    End
});

impl_diagnostics!(NotebookError {
    KernelInfo,
    Execute,
    Complete,
    Inspect,
    Interrupt,
    Restart,
    Shutdown
});

impl_diagnostics!(LspError {
    OpenDocument,
    ChangeDocument,
    SaveDocument,
    CloseDocument,
    Diagnostics,
    Hover,
    Definition,
    Completions,
    RenameSymbol,
    SemanticTokens,
    Cancel,
});

impl InteractionError {
    pub fn diagnostics(&self) -> &DiagnosticBundle {
        match self {
            InteractionError::CliInvoke { diagnostics } => diagnostics,
            InteractionError::Repl(err) => err.diagnostics(),
            InteractionError::Notebook(err) => err.diagnostics(),
            InteractionError::Lsp(err) => err.diagnostics(),
        }
    }

    pub fn into_diagnostics(self) -> DiagnosticBundle {
        match self {
            InteractionError::CliInvoke { diagnostics } => diagnostics,
            InteractionError::Repl(err) => err.into_diagnostics(),
            InteractionError::Notebook(err) => err.into_diagnostics(),
            InteractionError::Lsp(err) => err.into_diagnostics(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerivationArtifactError {
    Export { diagnostics: DiagnosticBundle },
    Validate { diagnostics: DiagnosticBundle },
}

impl_diagnostics!(DerivationArtifactError { Export, Validate });

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Info,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: String,
    pub category: String,
    pub severity: Severity,
    pub message: String,
    pub span: Option<Span>,
    /// Optional source identity (for example, a file URI) for multi-document diagnostics.
    pub source: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DiagnosticBundle {
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Identifier,
    Keyword,
    Symbol,
    Literal,
    Whitespace,
    Comment,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub lexeme: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Explicitness {
    Explicit,
    Implicit,
}

/// Type-safe projection index for product elimination.
/// Replaces raw `u8` to prevent out-of-range indices at the type level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProjIndex {
    First,
    Second,
}

impl fmt::Display for ProjIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProjIndex::First => write!(f, "1"),
            ProjIndex::Second => write!(f, "2"),
        }
    }
}

/// Figure 7 — type formation: C ::= α | B | C^op | [C,D] | Top | C × D
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CatType {
    /// Signature/base constructor (constant), not a bound variable.
    Base(String),
    Opposite(Box<CatType>),
    FunCat(Box<CatType>, Box<CatType>),
    Product(Box<CatType>, Box<CatType>),
    Top,
    /// Bound category variable.
    Var(String),
}

impl CatType {
    pub fn base(name: impl Into<String>) -> Self {
        Self::Base(name.into())
    }

    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    pub fn opposite(inner: CatType) -> Self {
        Self::Opposite(Box::new(inner))
    }

    pub fn fun_cat(domain: CatType, codomain: CatType) -> Self {
        Self::FunCat(Box::new(domain), Box::new(codomain))
    }

    pub fn product(left: CatType, right: CatType) -> Self {
        Self::Product(Box::new(left), Box::new(right))
    }

    pub fn from_expr(expr: &Expr) -> Result<Self, LanguageError> {
        match expr {
            Expr::Var(name) => Ok(CatType::Var(name.clone())),
            Expr::Opposite(inner) => Ok(CatType::Opposite(Box::new(CatType::from_expr(
                inner.as_ref(),
            )?))),
            Expr::Product { left, right } => Ok(CatType::Product(
                Box::new(CatType::from_expr(left.as_ref())?),
                Box::new(CatType::from_expr(right.as_ref())?),
            )),
            Expr::Arrow { parameter, result } => Ok(CatType::FunCat(
                Box::new(CatType::from_expr(parameter.as_ref())?),
                Box::new(CatType::from_expr(result.as_ref())?),
            )),
            Expr::Top => Ok(CatType::Top),
            other => Err(unexpected_expr_error("category type", other)),
        }
    }
}

fn unexpected_expr_error(target: &str, expr: &Expr) -> LanguageError {
    LanguageError::Syntax(SyntaxError::Parse {
        diagnostics: DiagnosticBundle {
            diagnostics: vec![Diagnostic {
                code: "unexpected_expression".to_string(),
                category: "unexpected_expression".to_string(),
                severity: Severity::Error,
                message: format!("cannot interpret expression as {target}: {expr}"),
                span: None,
                source: None,
            }],
        },
    })
}

impl fmt::Display for CatType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CatType::Base(name) => write!(f, "{name}"),
            // Apostrophe is an internal disambiguating pretty-print convention.
            // It is not part of the user-facing surface syntax contract.
            CatType::Var(name) => write!(f, "'{name}"),
            CatType::Opposite(inner) => write!(f, "({inner})^"),
            CatType::FunCat(domain, codomain) => write!(f, "[{domain}, {codomain}]"),
            CatType::Product(left, right) => write!(f, "({left} * {right})"),
            CatType::Top => write!(f, "Top"),
        }
    }
}

/// Binder for term-level and type-level variables. Binds a name to a category type.
/// Used in lambdas (Figure 8), ends/coends (Figure 9), and surface syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TermBinder {
    pub name: String,
    pub ty: Box<CatType>,
    pub explicitness: Explicitness,
}

impl TermBinder {
    pub fn explicit(name: impl Into<String>, ty: CatType) -> Self {
        Self {
            name: name.into(),
            ty: Box::new(ty),
            explicitness: Explicitness::Explicit,
        }
    }

    pub fn implicit(name: impl Into<String>, ty: CatType) -> Self {
        Self {
            name: name.into(),
            ty: Box::new(ty),
            explicitness: Explicitness::Implicit,
        }
    }
}

/// Category-level binder: binds a name to a category type.
/// Used in core term lambdas (Figure 8), end/coend quantifiers (Figure 9),
/// and proof term end/coend constructs (Figures 11/16).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binder {
    pub name: String,
    pub ty: Box<CatType>,
}

impl Binder {
    pub fn new(name: impl Into<String>, ty: CatType) -> Self {
        Self {
            name: name.into(),
            ty: Box::new(ty),
        }
    }
}

/// Binder for proof-level variables. Binds a name to a predicate.
/// Used in proof term lambdas (Figure 11).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofBinder {
    pub name: String,
    pub ty: Box<Predicate>,
}

impl ProofBinder {
    pub fn new(name: impl Into<String>, ty: Predicate) -> Self {
        Self {
            name: name.into(),
            ty: Box::new(ty),
        }
    }
}

/// Figure 8 — core term syntax: F ::= x | λ(x:C).F | FG | (F,G) | πᵢ(F)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Lambda {
        binder: Binder,
        body: Box<Term>,
    },
    App {
        function: Box<Term>,
        argument: Box<Term>,
    },
    Pair {
        left: Box<Term>,
        right: Box<Term>,
    },
    Proj {
        tuple: Box<Term>,
        index: ProjIndex,
    },
}

impl Term {
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    pub fn lambda(binder: Binder, body: Term) -> Self {
        Self::Lambda {
            binder,
            body: Box::new(body),
        }
    }

    pub fn app(func: Term, arg: Term) -> Self {
        Self::App {
            function: Box::new(func),
            argument: Box::new(arg),
        }
    }

    pub fn pair(left: Term, right: Term) -> Self {
        Self::Pair {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn proj(tuple: Term, index: ProjIndex) -> Self {
        Self::Proj {
            tuple: Box::new(tuple),
            index,
        }
    }

    pub fn from_expr(expr: &Expr) -> Result<Self, LanguageError> {
        match expr {
            Expr::Var(name) => Ok(Term::Var(name.clone())),
            Expr::Lambda { binders, body } => {
                let core_body = Term::from_expr(body.as_ref())?;
                Ok(binders.iter().rev().fold(core_body, |acc, b| Term::Lambda {
                    binder: Binder::new(b.name.clone(), (*b.ty).clone()),
                    body: Box::new(acc),
                }))
            }
            Expr::App {
                function,
                arguments,
            } => {
                let func = Term::from_expr(function.as_ref())?;
                arguments.iter().try_fold(func, |acc, arg_expr| {
                    let arg = Term::from_expr(arg_expr)?;
                    Ok(Term::App {
                        function: Box::new(acc),
                        argument: Box::new(arg),
                    })
                })
            }
            Expr::Pair { left, right } => Ok(Term::Pair {
                left: Box::new(Term::from_expr(left.as_ref())?),
                right: Box::new(Term::from_expr(right.as_ref())?),
            }),
            Expr::Proj { tuple, index } => Ok(Term::Proj {
                tuple: Box::new(Term::from_expr(tuple.as_ref())?),
                index: *index,
            }),
            other => Err(unexpected_expr_error("term", other)),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name) => write!(f, "{name}"),
            Term::Lambda { binder, body } => {
                write!(f, "\\({} : {}). {body}", binder.name, binder.ty)
            }
            Term::App { function, argument } => write!(f, "({function} {argument})"),
            Term::Pair { left, right } => write!(f, "({left}, {right})"),
            Term::Proj { tuple, index } => write!(f, "({tuple}).{index}"),
        }
    }
}

/// Figure 9 — predicate well-formedness
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Predicate {
    Top,
    Conj {
        left: Box<Predicate>,
        right: Box<Predicate>,
    },
    Hom {
        category: CatType,
        source: Term,
        target: Term,
    },
    End {
        binder: Binder,
        body: Box<Predicate>,
    },
    Coend {
        binder: Binder,
        body: Box<Predicate>,
    },
    Opposite(Box<Predicate>),
    Var(String),
    App {
        predicate: Box<Predicate>,
        arguments: Vec<Term>,
    },
    Arrow {
        antecedent: Box<Predicate>,
        consequent: Box<Predicate>,
    },
}

impl Predicate {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn conj(left: Predicate, right: Predicate) -> Self {
        Self::Conj {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn hom(category: CatType, source: Term, target: Term) -> Self {
        Self::Hom {
            category,
            source,
            target,
        }
    }

    pub fn end_form(binder: Binder, body: Predicate) -> Self {
        Self::End {
            binder,
            body: Box::new(body),
        }
    }

    pub fn coend_form(binder: Binder, body: Predicate) -> Self {
        Self::Coend {
            binder,
            body: Box::new(body),
        }
    }

    pub fn opposite(inner: Predicate) -> Self {
        Self::Opposite(Box::new(inner))
    }

    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    pub fn app(pred: Predicate, args: Vec<Term>) -> Self {
        Self::App {
            predicate: Box::new(pred),
            arguments: args,
        }
    }

    pub fn arrow(antecedent: Predicate, consequent: Predicate) -> Self {
        Self::Arrow {
            antecedent: Box::new(antecedent),
            consequent: Box::new(consequent),
        }
    }

    pub fn from_expr(expr: &Expr) -> Result<Self, LanguageError> {
        match expr {
            Expr::Hom {
                category,
                source,
                target,
            } => Ok(Predicate::Hom {
                category: CatType::from_expr(category.as_ref())?,
                source: Term::from_expr(source.as_ref())?,
                target: Term::from_expr(target.as_ref())?,
            }),
            Expr::End { binder, body } => Ok(Predicate::End {
                binder: Binder::new(binder.name.clone(), (*binder.ty).clone()),
                body: Box::new(Predicate::from_expr(body.as_ref())?),
            }),
            Expr::Coend { binder, body } => Ok(Predicate::Coend {
                binder: Binder::new(binder.name.clone(), (*binder.ty).clone()),
                body: Box::new(Predicate::from_expr(body.as_ref())?),
            }),
            Expr::Top => Ok(Predicate::Top),
            Expr::Var(name) => Ok(Predicate::Var(name.clone())),
            Expr::Opposite(inner) => Ok(Predicate::Opposite(Box::new(Predicate::from_expr(
                inner.as_ref(),
            )?))),
            Expr::Product { left, right } => Ok(Predicate::Conj {
                left: Box::new(Predicate::from_expr(left.as_ref())?),
                right: Box::new(Predicate::from_expr(right.as_ref())?),
            }),
            Expr::Arrow { parameter, result } => Ok(Predicate::Arrow {
                antecedent: Box::new(Predicate::from_expr(parameter.as_ref())?),
                consequent: Box::new(Predicate::from_expr(result.as_ref())?),
            }),
            Expr::App {
                function,
                arguments,
            } => Ok(Predicate::App {
                predicate: Box::new(Predicate::from_expr(function.as_ref())?),
                arguments: arguments
                    .iter()
                    .map(Term::from_expr)
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            other => Err(unexpected_expr_error("predicate", other)),
        }
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Predicate::Top => write!(f, "Top"),
            Predicate::Conj { left, right } => write!(f, "({left} * {right})"),
            Predicate::Hom {
                category,
                source,
                target,
            } => write!(f, "({source} ->[{category}] {target})"),
            Predicate::End { binder, body } => {
                write!(f, "(end ({} : {}) . {body})", binder.name, binder.ty)
            }
            Predicate::Coend { binder, body } => {
                write!(f, "(coend ({} : {}) . {body})", binder.name, binder.ty)
            }
            Predicate::Opposite(inner) => write!(f, "({inner})^"),
            Predicate::Var(name) => write!(f, "{name}"),
            Predicate::App {
                predicate,
                arguments,
            } => {
                write!(f, "({predicate}")?;
                for arg in arguments {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            Predicate::Arrow {
                antecedent,
                consequent,
            } => write!(f, "({antecedent} -> {consequent})"),
        }
    }
}

/// Figures 11/16 — entailment typing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofTerm {
    Var(String),
    Lambda {
        binder: ProofBinder,
        body: Box<ProofTerm>,
    },
    App {
        function: Box<ProofTerm>,
        argument: Box<ProofTerm>,
    },
    Pair {
        left: Box<ProofTerm>,
        right: Box<ProofTerm>,
    },
    Proj {
        proof: Box<ProofTerm>,
        index: ProjIndex,
    },
    Refl {
        term: Term,
    },
    JElim {
        transport: Box<ProofTerm>,
        path: Box<ProofTerm>,
    },
    EndIntro {
        binder: Binder,
        body: Box<ProofTerm>,
    },
    EndElim {
        proof: Box<ProofTerm>,
        witness: Term,
    },
    CoendIntro {
        witness: Term,
        body: Box<ProofTerm>,
    },
    CoendElim {
        proof: Box<ProofTerm>,
        binder: Binder,
        continuation: Box<ProofTerm>,
    },
}

impl ProofTerm {
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    pub fn lambda(binder: ProofBinder, body: ProofTerm) -> Self {
        Self::Lambda {
            binder,
            body: Box::new(body),
        }
    }

    pub fn app(function: ProofTerm, argument: ProofTerm) -> Self {
        Self::App {
            function: Box::new(function),
            argument: Box::new(argument),
        }
    }

    pub fn pair(left: ProofTerm, right: ProofTerm) -> Self {
        Self::Pair {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn proj(proof: ProofTerm, index: ProjIndex) -> Self {
        Self::Proj {
            proof: Box::new(proof),
            index,
        }
    }

    pub fn refl(term: Term) -> Self {
        Self::Refl { term }
    }

    pub fn j_elim(transport: ProofTerm, path: ProofTerm) -> Self {
        Self::JElim {
            transport: Box::new(transport),
            path: Box::new(path),
        }
    }

    pub fn end_intro(binder: Binder, body: ProofTerm) -> Self {
        Self::EndIntro {
            binder,
            body: Box::new(body),
        }
    }

    pub fn end_elim(proof: ProofTerm, witness: Term) -> Self {
        Self::EndElim {
            proof: Box::new(proof),
            witness,
        }
    }

    pub fn coend_intro(witness: Term, body: ProofTerm) -> Self {
        Self::CoendIntro {
            witness,
            body: Box::new(body),
        }
    }

    pub fn coend_elim(proof: ProofTerm, binder: Binder, continuation: ProofTerm) -> Self {
        Self::CoendElim {
            proof: Box::new(proof),
            binder,
            continuation: Box::new(continuation),
        }
    }

    pub fn from_expr(expr: &Expr) -> Result<Self, LanguageError> {
        match expr {
            Expr::Var(name) => Ok(ProofTerm::Var(name.clone())),
            Expr::App {
                function,
                arguments,
            } => {
                let func = ProofTerm::from_expr(function.as_ref())?;
                arguments.iter().try_fold(func, |acc, arg_expr| {
                    let arg = ProofTerm::from_expr(arg_expr)?;
                    Ok(ProofTerm::App {
                        function: Box::new(acc),
                        argument: Box::new(arg),
                    })
                })
            }
            Expr::Refl { term } => Ok(ProofTerm::Refl {
                term: Term::from_expr(term.as_ref())?,
            }),
            Expr::JElim { transport, path } => Ok(ProofTerm::JElim {
                transport: Box::new(ProofTerm::from_expr(transport.as_ref())?),
                path: Box::new(ProofTerm::from_expr(path.as_ref())?),
            }),
            Expr::Pair { left, right } => Ok(ProofTerm::Pair {
                left: Box::new(ProofTerm::from_expr(left.as_ref())?),
                right: Box::new(ProofTerm::from_expr(right.as_ref())?),
            }),
            Expr::Proj { tuple, index } => Ok(ProofTerm::Proj {
                proof: Box::new(ProofTerm::from_expr(tuple.as_ref())?),
                index: *index,
            }),
            Expr::EndIntro { binder, body } => Ok(ProofTerm::EndIntro {
                binder: binder.clone(),
                body: Box::new(ProofTerm::from_expr(body.as_ref())?),
            }),
            Expr::EndElim { proof, witness } => Ok(ProofTerm::EndElim {
                proof: Box::new(ProofTerm::from_expr(proof.as_ref())?),
                witness: Term::from_expr(witness.as_ref())?,
            }),
            Expr::CoendIntro { witness, body } => Ok(ProofTerm::CoendIntro {
                witness: Term::from_expr(witness.as_ref())?,
                body: Box::new(ProofTerm::from_expr(body.as_ref())?),
            }),
            Expr::CoendElim {
                proof,
                binder,
                continuation,
            } => Ok(ProofTerm::CoendElim {
                proof: Box::new(ProofTerm::from_expr(proof.as_ref())?),
                binder: binder.clone(),
                continuation: Box::new(ProofTerm::from_expr(continuation.as_ref())?),
            }),
            // Lambda is sort-ambiguous: Expr::Lambda binds term variables (TermBinder
            // with CatType), but ProofTerm::Lambda binds proof variables (ProofBinder
            // with Predicate). Disambiguation is the elaborator's job, not from_expr's.
            other => Err(unexpected_expr_error("proof term", other)),
        }
    }
}

impl fmt::Display for ProofTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofTerm::Var(name) => write!(f, "{name}"),
            ProofTerm::Lambda { binder, body } => {
                write!(f, "\\({} : {}). {body}", binder.name, binder.ty)
            }
            ProofTerm::App { function, argument } => write!(f, "({function} {argument})"),
            ProofTerm::Pair { left, right } => write!(f, "({left}, {right})"),
            ProofTerm::Proj { proof, index } => write!(f, "({proof}).{index}"),
            ProofTerm::Refl { term } => write!(f, "refl {term}"),
            ProofTerm::JElim { transport, path } => write!(f, "J {transport} {path}"),
            ProofTerm::EndIntro { binder, body } => {
                write!(f, "end ({} : {}) . {body}", binder.name, binder.ty)
            }
            ProofTerm::EndElim { proof, witness } => write!(f, "end^-1 {proof} {witness}"),
            ProofTerm::CoendIntro { witness, body } => write!(f, "coend {witness} {body}"),
            ProofTerm::CoendElim {
                proof,
                binder,
                continuation,
            } => {
                write!(
                    f,
                    "coend^-1 {proof} ({} : {}) . {continuation}",
                    binder.name, binder.ty
                )
            }
        }
    }
}

/// Surface syntax extension for tuple/wildcard patterns.
/// Not part of the paper's core calculus and must be desugared before type-checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SurfacePattern {
    Var(String),
    Pair(Box<SurfacePattern>, Box<SurfacePattern>),
    Wildcard,
    Annotated(Box<SurfacePattern>, Box<CatType>),
}

impl SurfacePattern {
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    pub fn pair(left: SurfacePattern, right: SurfacePattern) -> Self {
        Self::Pair(Box::new(left), Box::new(right))
    }

    pub fn annotated(pattern: SurfacePattern, ty: CatType) -> Self {
        Self::Annotated(Box::new(pattern), Box::new(ty))
    }

    pub fn bound_variables(&self) -> Vec<&str> {
        fn collect<'a>(pattern: &'a SurfacePattern, out: &mut Vec<&'a str>) {
            match pattern {
                SurfacePattern::Var(name) => out.push(name),
                SurfacePattern::Pair(left, right) => {
                    collect(left, out);
                    collect(right, out);
                }
                SurfacePattern::Wildcard => {}
                SurfacePattern::Annotated(inner, _) => collect(inner, out),
            }
        }

        let mut variables = Vec::new();
        collect(self, &mut variables);
        variables
    }
}

impl fmt::Display for SurfacePattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SurfacePattern::Var(name) => write!(f, "{name}"),
            SurfacePattern::Pair(left, right) => write!(f, "({left}, {right})"),
            SurfacePattern::Wildcard => write!(f, "_"),
            SurfacePattern::Annotated(pattern, ty) => write!(f, "({pattern} : {ty})"),
        }
    }
}

/// Surface let-expression with optional type annotation.
/// Groups pattern, annotation, value, and body into a single struct
/// for use in `Expr::Let`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SurfaceLetExpr {
    pub pattern: SurfacePattern,
    pub annotation: Option<Box<Expr>>,
    pub value: Box<Expr>,
    pub body: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextBinding {
    pub name: String,
    pub ty: CatType,
    pub variance: Variance,
}

impl ContextBinding {
    pub fn new(name: &str, ty: CatType, variance: Variance) -> Self {
        Self {
            name: name.to_string(),
            ty,
            variance,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Context {
    bindings: Vec<ContextBinding>,
}

impl Context {
    /// Primitive context extension: Γ, x:C (Figure 8).
    pub fn extend(mut self, binding: ContextBinding) -> Self {
        self.bindings.push(binding);
        self
    }

    /// Weakening admissibility: adding unused assumptions preserves typing.
    /// This is an admissible structural rule, not a primitive rule.
    pub fn weaken(mut self, assumptions: Vec<ContextBinding>) -> Self {
        self.bindings.extend(assumptions);
        self
    }

    pub fn exchange(mut self, left: usize, right: usize) -> Option<Self> {
        if left >= self.bindings.len() || right >= self.bindings.len() {
            return None;
        }
        self.bindings.swap(left, right);
        Some(self)
    }

    /// Apply type-level opposite to each binding type and flip variance.
    ///
    /// Follows Figure 7 and Figures 13/14: `(Gamma, C)^op = Gamma^op, C^op`.
    /// Covariant ↔ Contravariant are flipped; Dinatural and Unused are preserved.
    /// Double-opposite is reduced: `(C^op)^op = C`.
    pub fn opposite(self) -> Self {
        let bindings = self
            .bindings
            .into_iter()
            .map(|binding| {
                let flipped_variance = match binding.variance {
                    Variance::Covariant => Variance::Contravariant,
                    Variance::Contravariant => Variance::Covariant,
                    other => other,
                };
                ContextBinding {
                    ty: match binding.ty {
                        CatType::Opposite(inner) => *inner,
                        other => CatType::Opposite(Box::new(other)),
                    },
                    variance: flipped_variance,
                    ..binding
                }
            })
            .collect();
        Self { bindings }
    }

    pub fn bindings(&self) -> &[ContextBinding] {
        &self.bindings
    }

    pub fn lookup(&self, name: &str) -> Option<&ContextBinding> {
        self.bindings
            .iter()
            .rev()
            .find(|binding| binding.name == name)
    }

    pub fn contains(&self, name: &str) -> bool {
        self.lookup(name).is_some()
    }
}

/// Surface expression syntax spanning Figures 8/9/11/16 plus surface sugar
/// (let, tuple patterns, implicit arguments).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Lambda {
        binders: Vec<TermBinder>,
        body: Box<Expr>,
    },
    App {
        function: Box<Expr>,
        arguments: Vec<Expr>,
    },
    Hom {
        category: Box<Expr>,
        source: Box<Expr>,
        target: Box<Expr>,
    },
    Product {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Arrow {
        parameter: Box<Expr>,
        result: Box<Expr>,
    },
    End {
        binder: Binder,
        body: Box<Expr>,
    },
    Coend {
        binder: Binder,
        body: Box<Expr>,
    },
    Opposite(Box<Expr>),
    EndIntro {
        binder: Binder,
        body: Box<Expr>,
    },
    EndElim {
        proof: Box<Expr>,
        witness: Box<Expr>,
    },
    CoendIntro {
        witness: Box<Expr>,
        body: Box<Expr>,
    },
    CoendElim {
        proof: Box<Expr>,
        binder: Binder,
        continuation: Box<Expr>,
    },
    Refl {
        term: Box<Expr>,
    },
    JElim {
        transport: Box<Expr>,
        path: Box<Expr>,
    },
    Proj {
        tuple: Box<Expr>,
        index: ProjIndex,
    },
    Pair {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Var(String),
    Let(SurfaceLetExpr),
    Top,
}

impl Expr {
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    pub fn app(func: Expr, args: Vec<Expr>) -> Self {
        Self::App {
            function: Box::new(func),
            arguments: args,
        }
    }

    pub fn lambda(binders: Vec<TermBinder>, body: Expr) -> Self {
        Self::Lambda {
            binders,
            body: Box::new(body),
        }
    }

    pub fn arrow(domain: Expr, codomain: Expr) -> Self {
        Self::Arrow {
            parameter: Box::new(domain),
            result: Box::new(codomain),
        }
    }

    pub fn hom(cat: Expr, source: Expr, target: Expr) -> Self {
        Self::Hom {
            category: Box::new(cat),
            source: Box::new(source),
            target: Box::new(target),
        }
    }

    pub fn product(left: Expr, right: Expr) -> Self {
        Self::Product {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn end_form(binder: Binder, body: Expr) -> Self {
        Self::End {
            binder,
            body: Box::new(body),
        }
    }

    pub fn coend_form(binder: Binder, body: Expr) -> Self {
        Self::Coend {
            binder,
            body: Box::new(body),
        }
    }

    pub fn refl(term: Expr) -> Self {
        Self::Refl {
            term: Box::new(term),
        }
    }

    pub fn j_elim(transport: Expr, path: Expr) -> Self {
        Self::JElim {
            transport: Box::new(transport),
            path: Box::new(path),
        }
    }

    pub fn opposite(inner: Expr) -> Self {
        Self::Opposite(Box::new(inner))
    }

    pub fn end_intro(binder: Binder, body: Expr) -> Self {
        Self::EndIntro {
            binder,
            body: Box::new(body),
        }
    }

    pub fn end_elim(proof: Expr, witness: Expr) -> Self {
        Self::EndElim {
            proof: Box::new(proof),
            witness: Box::new(witness),
        }
    }

    pub fn coend_intro(witness: Expr, body: Expr) -> Self {
        Self::CoendIntro {
            witness: Box::new(witness),
            body: Box::new(body),
        }
    }

    pub fn coend_elim(proof: Expr, binder: Binder, continuation: Expr) -> Self {
        Self::CoendElim {
            proof: Box::new(proof),
            binder,
            continuation: Box::new(continuation),
        }
    }

    pub fn proj(tuple: Expr, index: ProjIndex) -> Self {
        Self::Proj {
            tuple: Box::new(tuple),
            index,
        }
    }

    pub fn pair(left: Expr, right: Expr) -> Self {
        Self::Pair {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn as_lambda(&self) -> Option<(&[TermBinder], &Expr)> {
        match self {
            Self::Lambda { binders, body } => Some((binders, body)),
            _ => None,
        }
    }

    pub fn as_app(&self) -> Option<(&Expr, &[Expr])> {
        match self {
            Self::App {
                function,
                arguments,
            } => Some((function, arguments)),
            _ => None,
        }
    }

    pub fn as_var(&self) -> Option<&str> {
        match self {
            Self::Var(name) => Some(name),
            _ => None,
        }
    }

    pub fn as_end_intro(&self) -> Option<(&Binder, &Expr)> {
        match self {
            Self::EndIntro { binder, body } => Some((binder, body)),
            _ => None,
        }
    }

    pub fn as_end_elim(&self) -> Option<(&Expr, &Expr)> {
        match self {
            Self::EndElim { proof, witness } => Some((proof, witness)),
            _ => None,
        }
    }

    pub fn as_coend_intro(&self) -> Option<(&Expr, &Expr)> {
        match self {
            Self::CoendIntro { witness, body } => Some((witness, body)),
            _ => None,
        }
    }

    pub fn as_coend_elim(&self) -> Option<(&Expr, &Binder, &Expr)> {
        match self {
            Self::CoendElim {
                proof,
                binder,
                continuation,
            } => Some((proof, binder, continuation)),
            _ => None,
        }
    }

    pub fn let_expr(
        pattern: SurfacePattern,
        annotation: Option<Expr>,
        value: Expr,
        body: Expr,
    ) -> Self {
        Self::Let(SurfaceLetExpr {
            pattern,
            annotation: annotation.map(Box::new),
            value: Box::new(value),
            body: Box::new(body),
        })
    }

    pub fn as_let(&self) -> Option<&SurfaceLetExpr> {
        match self {
            Self::Let(let_expr) => Some(let_expr),
            _ => None,
        }
    }

    /// Convert a core `Term` back to a surface `Expr`.
    /// This is the inverse of `Term::from_expr` (modulo surface sugar).
    /// Used for re-normalization of already-normalized terms.
    pub fn from_term(term: &Term) -> Self {
        match term {
            Term::Var(name) => Expr::Var(name.clone()),
            Term::Lambda { binder, body } => Expr::Lambda {
                binders: vec![TermBinder::explicit(
                    binder.name.clone(),
                    (*binder.ty).clone(),
                )],
                body: Box::new(Expr::from_term(body)),
            },
            Term::App { function, argument } => Expr::App {
                function: Box::new(Expr::from_term(function)),
                arguments: vec![Expr::from_term(argument)],
            },
            Term::Pair { left, right } => Expr::Pair {
                left: Box::new(Expr::from_term(left)),
                right: Box::new(Expr::from_term(right)),
            },
            Term::Proj { tuple, index } => Expr::Proj {
                tuple: Box::new(Expr::from_term(tuple)),
                index: *index,
            },
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Lambda { binders, body } => {
                write!(f, "\\")?;
                for (index, binder) in binders.iter().enumerate() {
                    if index > 0 {
                        write!(f, " ")?;
                    }
                    match binder.explicitness {
                        Explicitness::Explicit => {
                            write!(f, "({} : {})", binder.name, binder.ty)?;
                        }
                        Explicitness::Implicit => {
                            write!(f, "{{{} : {}}}", binder.name, binder.ty)?;
                        }
                    }
                }
                write!(f, ". {body}")
            }
            Expr::App {
                function,
                arguments,
            } => {
                write!(f, "({function}")?;
                for argument in arguments {
                    write!(f, " {argument}")?;
                }
                write!(f, ")")
            }
            Expr::Hom {
                category,
                source,
                target,
            } => write!(f, "({source} ->[{category}] {target})"),
            Expr::Product { left, right } => write!(f, "({left} * {right})"),
            Expr::Arrow { parameter, result } => write!(f, "({parameter} -> {result})"),
            Expr::End { binder, body } => {
                write!(f, "(end ({} : {}) . {body})", binder.name, binder.ty)
            }
            Expr::Coend { binder, body } => {
                write!(f, "(coend ({} : {}) . {body})", binder.name, binder.ty)
            }
            Expr::Opposite(inner) => write!(f, "({inner})^"),
            Expr::EndIntro { binder, body } => {
                write!(f, "end ({} : {}) . {body}", binder.name, binder.ty)
            }
            Expr::EndElim { proof, witness } => write!(f, "end^-1 {proof} {witness}"),
            Expr::CoendIntro { witness, body } => write!(f, "coend {witness} {body}"),
            Expr::CoendElim {
                proof,
                binder,
                continuation,
            } => {
                write!(
                    f,
                    "coend^-1 {proof} ({} : {}) . {continuation}",
                    binder.name, binder.ty
                )
            }
            Expr::Refl { term } => write!(f, "refl {term}"),
            Expr::JElim { transport, path } => write!(f, "J {transport} {path}"),
            Expr::Proj { tuple, index } => write!(f, "({tuple}).{index}"),
            Expr::Pair { left, right } => write!(f, "({left}, {right})"),
            Expr::Var(name) => write!(f, "{name}"),
            Expr::Let(let_expr) => {
                write!(f, "let {}", let_expr.pattern)?;
                if let Some(ann) = &let_expr.annotation {
                    write!(f, " : {ann}")?;
                }
                write!(f, " = {} in {}", let_expr.value, let_expr.body)
            }
            Expr::Top => write!(f, "Top"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declaration {
    Postulate {
        name: String,
        ty: Expr,
    },
    Definition {
        name: String,
        binders: Vec<TermBinder>,
        ty: Expr,
        value: Expr,
    },
}

impl Declaration {
    pub fn name(&self) -> &str {
        match self {
            Self::Postulate { name, .. } | Self::Definition { name, .. } => name,
        }
    }

    pub fn is_definition(&self) -> bool {
        matches!(self, Self::Definition { .. })
    }

    pub fn is_postulate(&self) -> bool {
        matches!(self, Self::Postulate { .. })
    }

    pub fn type_annotation(&self) -> &Expr {
        match self {
            Self::Postulate { ty, .. } | Self::Definition { ty, .. } => ty,
        }
    }

    pub fn definition_value(&self) -> Option<&Expr> {
        match self {
            Self::Definition { value, .. } => Some(value),
            _ => None,
        }
    }

    pub fn definition_binders(&self) -> Option<&[TermBinder]> {
        match self {
            Self::Definition { binders, .. } => Some(binders),
            _ => None,
        }
    }
}

/// Items that can appear inside a `SurfaceModule`.
/// Separates the concept of nested modules from core declarations (which have
/// no Module variant and correspond directly to the paper's declaration forms).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleItem {
    Declaration(Declaration),
    SubModule {
        name: String,
        items: Vec<ModuleItem>,
    },
}

/// A dot-separated qualified name (e.g., `Data.List.Base`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QualifiedName(pub Vec<String>);

impl fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for component in &self.0 {
            if !first {
                write!(f, ".")?;
            }
            write!(f, "{component}")?;
            first = false;
        }
        Ok(())
    }
}

/// Filter for selective imports: `using (a, b)` or `hiding (c, d)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportFilter {
    Using(Vec<String>),
    Hiding(Vec<String>),
}

/// A single name renaming in an import clause: `original as renamed`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportRenaming {
    pub original: String,
    pub renamed: String,
}

/// A full import clause: `import Path.To.Module [as Alias] [using/hiding (...)] [renaming ...]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportClause {
    pub path: QualifiedName,
    pub alias: Option<String>,
    pub filter: Option<ImportFilter>,
    pub renamings: Vec<ImportRenaming>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SurfaceModule {
    pub name: Option<QualifiedName>,
    pub imports: Vec<ImportClause>,
    pub items: Vec<ModuleItem>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedDeclaration {
    pub declaration: Declaration,
    pub elaborated_type: ElaboratedType,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TypedModule {
    /// Optional module name from the corresponding surface module.
    pub name: Option<QualifiedName>,
    /// Import clauses from the corresponding surface module.
    pub imports: Vec<ImportClause>,
    pub declarations: Vec<TypedDeclaration>,
}

impl TypedModule {
    pub fn with_surface_metadata(
        name: Option<QualifiedName>,
        imports: Vec<ImportClause>,
        declarations: Vec<TypedDeclaration>,
    ) -> Self {
        Self {
            name,
            imports,
            declarations,
        }
    }

    pub fn from_declarations(declarations: Vec<TypedDeclaration>) -> Self {
        Self {
            name: None,
            imports: Vec::new(),
            declarations,
        }
    }

    pub fn lookup_declaration(&self, name: &str) -> Option<&TypedDeclaration> {
        self.declarations
            .iter()
            .find(|typed| typed.declaration.name() == name)
    }

    pub fn postulates(&self) -> impl Iterator<Item = &TypedDeclaration> {
        self.declarations
            .iter()
            .filter(|typed| typed.declaration.is_postulate())
    }

    pub fn definitions(&self) -> impl Iterator<Item = &TypedDeclaration> {
        self.declarations
            .iter()
            .filter(|typed| typed.declaration.is_definition())
    }
}

/// The elaborated type of a declaration, which may be either a category type
/// (for term-level declarations) or a predicate (for proof-level declarations).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElaboratedType {
    Cat(CatType),
    Pred(Predicate),
}

/// Sort-resolved expression payload emitted after elaboration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedExpr {
    CatType(CatType),
    Term(Term),
    Predicate(Predicate),
    ProofTerm(ProofTerm),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diterm {
    pub context: Context,
    pub term: Term,
    pub ty: CatType,
}

impl Diterm {
    pub fn new(context: Context, term: Term, ty: CatType) -> Self {
        Self { context, term, ty }
    }

    pub fn negative_ctx(&self) -> Context {
        self.context.clone().opposite()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalForm {
    pub(crate) structure: Term,
    pub(crate) ty: CatType,
}

impl NormalForm {
    pub(crate) fn new(structure: Term, ty: CatType) -> Self {
        Self { structure, ty }
    }

    pub fn structure(&self) -> &Term {
        &self.structure
    }

    pub fn ty(&self) -> &CatType {
        &self.ty
    }

    pub fn head_constructor(&self) -> &Term {
        fn app_head(term: &Term) -> &Term {
            match term {
                Term::App { function, .. } => app_head(function),
                _ => term,
            }
        }
        app_head(&self.structure)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvaluationOutcome {
    /// Stable textual rendering for CLI/REPL/notebook output surfaces.
    pub value: String,
    /// Structured evaluation result when available.
    pub structure: Option<Term>,
    pub value_type: CatType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Variance {
    Covariant,
    Contravariant,
    Dinatural,
    Unused,
}

impl Variance {
    /// Definition 2.5: A transformation is natural iff it is covariant or contravariant.
    /// Dinatural transformations are not natural.
    pub fn is_natural(&self) -> bool {
        matches!(self, Variance::Covariant | Variance::Contravariant)
    }

    pub fn is_unused(&self) -> bool {
        matches!(self, Variance::Unused)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarianceOccurrence {
    /// AST path from predicate root to this occurrence (sequence of child indices).
    /// Used for diagnostic position reporting.
    pub path: Vec<usize>,
    pub local_variance: Variance,
}

/// Per-variable variance classification for a predicate family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarianceAnalysis {
    pub variable: String,
    pub variance: Variance,
    pub occurrences: Vec<VarianceOccurrence>,
}

impl VarianceAnalysis {
    pub fn is_unused(&self) -> bool {
        self.variance.is_unused()
    }
}

/// Proof-term-constructing derivation rules.
///
/// Proof-term-constructing derivation rules (Figures 11, 16).
///
/// Equational/computation rules (Figures 11 JComp/JEq, Figure 16 iso/nat/din,
/// Figure 17 functoriality) are handled by the `Normalizer`. Variance rules
/// (Figures 10, 13, 14) are handled by the `VarianceChecker`. Context
/// membership (Figure 8) and prop-ctx well-formedness (Figure 9) are
/// `CheckJudgment` forms — they verify structure, not construct proof terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceRule {
    /// Figure 11: [Γ] Φ ⊢ α : P (variable/assumption rule).
    Var,
    /// Figure 11: [Γ] Φ ⊢ wk_P(α) : Q (weakening).
    Wk,
    /// Figure 11: [Γ] Φ ⊢ ! : ⊤ (top introduction).
    Top,
    /// Figure 11: reindexing with functors as terms.
    Idx,
    /// Figure 11: [Γ] P, Φ ⊢ contr_P(α) : Q (contraction).
    Contr,
    /// Figure 11: [Γ] Φ ⊢ P × Q (conjunction intro/elim).
    Prod,
    /// Figure 11: [Γ] Φ ⊢ P ⇒ Q (polarized implication intro/elim).
    Exp,
    /// Figure 11: [Γ] Φ ⊢ ∫_{x:C} P(x̄, x) (end rule).
    End,
    /// Figure 11: [Γ] Φ ⊢ ∫^{x:C} P(x̄, x) (coend rule).
    Coend,
    /// Figure 11: restricted dinatural cut via J.
    CutDin,
    /// Figure 11: restricted natural cut (composition of naturals).
    CutNat,
    /// Figure 11: refl_C : hom_C(x̄, x) (directed equality introduction).
    Refl,
    /// Figure 11: J(h)[e] (directed equality elimination).
    JRule,
    /// Figure 16: end introduction — [Γ] Φ ⊢ end(α) : ∫_{x:C} P(x̄, x).
    EndIntro,
    /// Figure 16: end elimination — [Γ] Φ ⊢ end⁻¹(α) : P(x̄, x).
    EndElim,
    /// Figure 16: coend elimination — [Γ] Φ ⊢ coend⁻¹(α, (x:C).β) : Q (uses counit of adjunction).
    CoendElim,
    /// Figure 16: coend introduction — [Γ] Φ ⊢ coend(t, α) : ∫^{x:C} P(x̄, x).
    CoendIntro,
}

impl InferenceRule {
    pub fn paper_rule_id(&self) -> &'static str {
        match self {
            Self::Var => "Figure11.Var",
            Self::Wk => "Figure11.Wk",
            Self::Top => "Figure11.Top",
            Self::Idx => "Figure11.Idx",
            Self::Contr => "Figure11.Contr",
            Self::Prod => "Figure11.Prod",
            Self::Exp => "Figure11.Exp",
            Self::End => "Figure11.End",
            Self::Coend => "Figure11.Coend",
            Self::CutDin => "Figure11.CutDin",
            Self::CutNat => "Figure11.CutNat",
            Self::Refl => "Figure11.Refl",
            Self::JRule => "Figure11.JRule",
            Self::EndIntro => "Figure16.EndIntro",
            Self::EndElim => "Figure16.EndElim",
            Self::CoendElim => "Figure16.CoendElim",
            Self::CoendIntro => "Figure16.CoendIntro",
        }
    }
}

impl fmt::Display for InferenceRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.paper_rule_id())
    }
}

/// The central entailment judgment form: [Γ] Φ ⊢ α : P.
/// This is the only derivation form that produces proof terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EntailmentJudgment {
    pub context: Context,
    pub propositions: Vec<Predicate>,
    pub proof_term: ProofTerm,
    pub goal: Predicate,
}

/// Judgment forms checked without producing proof terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckJudgment {
    TypeWellFormed(CatType),
    TypeEquality(CatType, CatType),
    ContextWellFormed(Context),
    VariableInContext(Context, String, CatType),
    PredicateWellFormed(Context, Predicate),
    PropCtxWellFormed(Context, Vec<Predicate>),
    TermTyping(Context, Term, CatType),
    EntailmentEquality(Context, Vec<Predicate>, ProofTerm, ProofTerm, Predicate),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleApplication {
    pub rule: InferenceRule,
    pub premises: Vec<RuleApplication>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleId(pub String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleText {
    pub name: String,
    pub source: String,
}

/// Import metadata on a module dependency edge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportSpec {
    pub alias: Option<String>,
    pub filter: Option<ImportFilter>,
    pub renamings: Vec<ImportRenaming>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGraph {
    pub modules: Vec<ModuleId>,
    pub edges: Vec<(ModuleId, ModuleId, ImportSpec)>,
}

impl ModuleGraph {
    /// Detect cycles in a module dependency graph via DFS.
    pub fn has_cycle(&self) -> bool {
        let mut adj: HashMap<&ModuleId, Vec<&ModuleId>> = HashMap::new();
        for (from, to, _spec) in &self.edges {
            adj.entry(from).or_default().push(to);
        }

        let mut visited = HashSet::new();
        let mut in_stack = HashSet::new();

        fn dfs<'a>(
            node: &'a ModuleId,
            adj: &HashMap<&'a ModuleId, Vec<&'a ModuleId>>,
            visited: &mut HashSet<&'a ModuleId>,
            in_stack: &mut HashSet<&'a ModuleId>,
        ) -> bool {
            visited.insert(node);
            in_stack.insert(node);
            if let Some(neighbors) = adj.get(node) {
                for neighbor in neighbors {
                    if !visited.contains(neighbor) {
                        if dfs(neighbor, adj, visited, in_stack) {
                            return true;
                        }
                    } else if in_stack.contains(neighbor) {
                        return true;
                    }
                }
            }
            in_stack.remove(node);
            false
        }

        for module in &self.modules {
            if !visited.contains(module) && dfs(module, &adj, &mut visited, &mut in_stack) {
                return true;
            }
        }
        false
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DerivationArtifact {
    pub judgment: EntailmentJudgment,
    pub rule: InferenceRule,
    pub root: RuleApplication,
}
