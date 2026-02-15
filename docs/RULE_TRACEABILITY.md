# Rule Traceability

Mapping of every paper rule (Figures 7-17) to its implementation location in the codebase.

Reference: Laretto, Loregian, Veltri — *Di- is for Directed* (POPL 2026).

## Type Definitions (`src/api/foundation.rs`)

| Paper Figure | Concern | Rust Type |
|---|---|---|
| Figure 7 | Type formation: `C ::= B \| C^op \| [C,D] \| Top \| C x D` | `CatType` |
| Figure 8 | Surface term constructors | `Expr` |
| Figure 9 | Predicate well-formedness | `Predicate` |
| Figure 11 | Proof term constructors | `ProofTerm` |

## Derivation Rules (`InferenceRule` via `TypeChecker::derive_judgment`)

21 variants — each constructs a proof term.

| Figure | Variant | Paper Rule |
|---|---|---|
| 8 | `CtxVarHere` | Γ, x : C ∋ x : C |
| 8 | `CtxVarThere` | Γ ∋ x : C ⟹ Γ, y : D ∋ x : C |
| 9 | `PropCtxEmpty` | · propctx |
| 9 | `PropCtxExtend` | Φ propctx ∧ P prop ⟹ P, Φ propctx |
| 11 | `Var` | [Γ] Φ ⊢ α : P |
| 11 | `Wk` | [Γ] Φ ⊢ wk_P(α) : Q |
| 11 | `Top` | [Γ] Φ ⊢ ! : ⊤ |
| 11 | `Idx` | Reindexing with functors |
| 11 | `Contr` | [Γ] P, Φ ⊢ contr_P(α) : Q |
| 11 | `Prod` | [Γ] Φ ⊢ P × Q |
| 11 | `Exp` | [Γ] Φ ⊢ P ⇒ Q |
| 11 | `End` | [Γ] Φ ⊢ ∫\_{x:C} P(x̄, x) |
| 11 | `Coend` | [Γ] Φ ⊢ ∫^{x:C} P(x̄, x) |
| 11 | `CutDin` | Restricted dinatural cut via J |
| 11 | `CutNat` | Restricted natural cut |
| 11 | `Refl` | refl\_C : hom\_C(x̄, x) |
| 11 | `JRule` | J(h)[e] — directed equality elimination |
| 16 | `EndIntro` | end(α) : ∫\_{x:C} P(x̄, x) |
| 16 | `EndElim` | end⁻¹(α) : P(x̄, x) |
| 16 | `CoendElim` | Counit of adjunction |
| 16 | `CoendIntro` | coend⁻¹(α) : ∫^{x:C} P(x̄, x) |

## Normalizer (`Normalizer::normalize_term`)

Equational and computation rules — no proof terms produced.

| Figure | Rule | Description |
|---|---|---|
| 7 | Judgmental equality | β/η for category-level types |
| 8 | β-reduction | (λx.M) N → M[N/x] |
| 8 | η-expansion | f → λx. f x |
| 11 | JComp | J(h)[refl z] → h z |
| 11 | JEq | Equational rule for J |
| 15 | Cut equations | Associativity, identity, coherence for cut |
| 16 | EndIsoL/EndIsoR | end⁻¹(end(α)) = α / end(end⁻¹(α)) = α |
| 16 | EndNatL/EndNatR | Naturality of end iso |
| 16 | EndDinL/EndDinR | Dinaturality of end iso |
| 16 | CoendIsoL/CoendIsoR | Coend iso equations |
| 16 | CoendNatL/CoendNatR | Naturality of coend iso |
| 16 | CoendDinL/CoendDinR | Dinaturality of coend iso |
| 17 | EndFunctoriality | Functoriality of end |
| 17 | CoendFunctoriality | Functoriality of coend |

## Variance Checker (`VarianceChecker::compute_variance_at_position`)

Variance and unused-variable rules — handled by dedicated trait.

| Figure | Rules | Description |
|---|---|---|
| 10 | CovHom, CovProd, CovExp, Contra, Unused | Basic variance classification |
| 13 | UnusedVarNeq, UnusedTop, UnusedApp, UnusedPair, UnusedProj, UnusedLambda, UnusedOp | Unused variable propagation |
| 14 | CovTopVariance, CovProdVariance, CovExpVariance, CovHomVariance, CovQuantifier, ContraVariance | Covariance/contravariance propagation |

## Parser/Elaborator (`Parser`, `TypeChecker::elaborate_module`)

| Figure | Concern | Implementation |
|---|---|---|
| 7 | Type well-formedness | `Parser::parse_module`, `TypeChecker::elaborate_module` |
| 8 | Context formation | `TypeChecker::elaborate_module` |
| 8 | Implicit argument resolution | `TypeChecker::elaborate_module` |
