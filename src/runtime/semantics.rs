use crate::api::*;

#[derive(Debug, Default)]
pub struct SemanticEngine {
    _private: (),
}

impl TypeChecker for SemanticEngine {
    fn elaborate_module(&self, _module: &SurfaceModule) -> Result<TypedModule, LanguageError> {
        unimplemented!("type_checker.elaborate_module")
    }

    fn infer_term_type(
        &self,
        _module: &TypedModule,
        _term: &Expr,
    ) -> Result<CatType, LanguageError> {
        unimplemented!("type_checker.infer_term_type")
    }

    fn derive(
        &self,
        _module: &TypedModule,
        _judgment: &EntailmentJudgment,
        _rule: InferenceRule,
    ) -> Result<RuleApplication, LanguageError> {
        unimplemented!("type_checker.derive")
    }

    fn check(&self, _module: &TypedModule, _judgment: &CheckJudgment) -> Result<(), LanguageError> {
        unimplemented!("type_checker.check")
    }
}

impl ExprResolver for SemanticEngine {
    fn resolve_expr(
        &self,
        _module: &TypedModule,
        _expr: &Expr,
    ) -> Result<ResolvedExpr, LanguageError> {
        unimplemented!("expr_resolver.resolve_expr")
    }
}

impl VarianceChecker for SemanticEngine {
    fn compute_variance_at_position(
        &self,
        _module: &TypedModule,
        _predicate: &str,
        _position_path: &[usize],
        _variable: &str,
    ) -> Result<Variance, LanguageError> {
        unimplemented!("variance_checker.compute_variance_at_position")
    }

    fn all_variances(
        &self,
        _module: &TypedModule,
        _predicate: &str,
    ) -> Result<Vec<VarianceAnalysis>, LanguageError> {
        unimplemented!("variance_checker.all_variances")
    }
}

impl Normalizer for SemanticEngine {
    fn normalize_term(
        &self,
        _module: &TypedModule,
        _term: &Expr,
    ) -> Result<NormalForm, LanguageError> {
        unimplemented!("normalizer.normalize_term")
    }

    fn definitionally_equal(
        &self,
        _module: &TypedModule,
        _left: &Expr,
        _right: &Expr,
    ) -> Result<bool, LanguageError> {
        unimplemented!("normalizer.definitionally_equal")
    }
}

impl Evaluator for SemanticEngine {
    fn evaluate_term(
        &self,
        _module: &TypedModule,
        _term: &Expr,
    ) -> Result<EvaluationOutcome, LanguageError> {
        unimplemented!("evaluator.evaluate_term")
    }
}

impl DerivationArtifacts for SemanticEngine {
    fn export_derivation_artifact(
        &self,
        _module: &TypedModule,
        _judgment: &EntailmentJudgment,
        _rule: InferenceRule,
    ) -> Result<DerivationArtifact, LanguageError> {
        unimplemented!("derivation.export_derivation_artifact")
    }

    fn validate_derivation_artifact(
        &self,
        _module: &TypedModule,
        _artifact: &DerivationArtifact,
    ) -> Result<(), LanguageError> {
        unimplemented!("derivation.validate_derivation_artifact")
    }
}
