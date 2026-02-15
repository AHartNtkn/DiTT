use super::*;

pub trait TypeChecker {
    fn elaborate_module(&self, module: &SurfaceModule) -> Result<TypedModule, LanguageError>;
    /// Type synthesis: Γ ⊢ F : C (Figure 8).
    fn infer_term_type(&self, module: &TypedModule, term: &Expr) -> Result<CatType, LanguageError>;
    /// Derive an entailment judgment [Γ] Φ ⊢ α : P using a specific inference rule.
    fn derive(
        &self,
        module: &TypedModule,
        judgment: &EntailmentJudgment,
        rule: InferenceRule,
    ) -> Result<RuleApplication, LanguageError>;
    /// Check a well-formedness or equality judgment (no proof term produced).
    fn check(&self, module: &TypedModule, judgment: &CheckJudgment) -> Result<(), LanguageError>;
}

pub trait VarianceChecker {
    /// Compute the variance at a specific AST path within a predicate body.
    /// Pass an empty path `&[]` for the aggregate (root-level) classification.
    fn compute_variance_at_position(
        &self,
        module: &TypedModule,
        predicate: &str,
        position_path: &[usize],
        variable: &str,
    ) -> Result<Variance, LanguageError>;
    /// Return variance analyses for every variable in the predicate, including occurrence data.
    /// Use this for tooling/reporting workflows that need whole-predicate coverage.
    fn all_variances(
        &self,
        module: &TypedModule,
        predicate: &str,
    ) -> Result<Vec<VarianceAnalysis>, LanguageError>;
}

pub trait Normalizer {
    fn normalize_term(
        &self,
        module: &TypedModule,
        term: &Expr,
    ) -> Result<NormalForm, LanguageError>;

    fn definitionally_equal(
        &self,
        module: &TypedModule,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, LanguageError>;
}

pub trait Evaluator {
    fn evaluate_term(
        &self,
        module: &TypedModule,
        term: &Expr,
    ) -> Result<EvaluationOutcome, LanguageError>;
}

/// Resolve a surface expression into a sort-specific core representation.
/// This separates parse-time syntax from elaborated sort information.
pub trait ExprResolver {
    fn resolve_expr(
        &self,
        module: &TypedModule,
        expr: &Expr,
    ) -> Result<ResolvedExpr, LanguageError>;
}

pub trait DerivationArtifacts {
    fn export_derivation_artifact(
        &self,
        module: &TypedModule,
        judgment: &EntailmentJudgment,
        rule: InferenceRule,
    ) -> Result<DerivationArtifact, LanguageError>;
    fn validate_derivation_artifact(
        &self,
        module: &TypedModule,
        artifact: &DerivationArtifact,
    ) -> Result<(), LanguageError>;
}
