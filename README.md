# DiTT

DiTT is an implementation of the first-order directed type theory from:

- Andrea Laretto, Fosco Loregian, Niccolo Veltri, *Di- is for Directed: First-Order Directed Type Theory via Dinaturality* (POPL 2026)
- PDF in this repo: `References/2409.10237v2.pdf`

In DiTT, types are categories, equality proofs are directed morphisms, and (co)ends serve as quantifiers. Unlike Homotopy Type Theory, where paths are invertible, DiTT's morphisms are one-way --- capturing the mathematical reality of categories.

## Current Status

The type checker, parser, normalizer, and evaluator are implemented. The standard library contains 15 modules of verified category theory constructions. All contract tests pass.

## Surface Syntax

DiTT uses an Agda-like syntax with built-ins for directed constructs. Unicode is the default; ASCII is accepted as a fallback.

| Concept | Unicode (default) | ASCII fallback |
|---|---|---|
| Lambda | `λx. body` | `\x. body` |
| Arrow / implication | `A → B` | `A -> B` |
| Directed hom | `a →[C] b` | `a ->[C] b` |
| End (universal) | `∫ (x : C). P x` | `end (x : C). P x` |
| Coend (existential) | `∫^ (x : C). P x` | `coend (x : C). P x` |
| Product | `A × B` | `A * B` |
| Opposite category | `C^` | `C^` |
| Identity morphism | `refl x` | `refl x` |
| J eliminator | `J h [f]` | `J h [f]` |

## Standard Library

15 modules in `stdlib/`, each self-contained with its own postulates:

| Module | Contents |
|---|---|
| `Category` | Identity morphism |
| `Morphism` | Composition, identity laws, associativity, opposite hom isomorphism |
| `Functor` | Functorial action on morphisms, identity and composition laws |
| `NatTrans` | Natural transformations, vertical/horizontal composition, whiskering, dinaturals |
| `Yoneda` | Transport, Yoneda forward/backward, round-trips, embedding, full faithfulness |
| `EndCoend` | Fubini, product/implication preservation, currying, singleton, end-to-coend |
| `KanExtension` | Right/left Kan extensions, unit/counit maps |
| `Adjunction` | Hom-isomorphism, unit/counit, triangle identity composites |
| `Profunctor` | Hom profunctor, composition, representable profunctors, right lifts |
| `Presheaf` | Presheaf exponential, evaluation, currying, Day convolution |
| `Codensity` | Codensity monad (Ran_Id P), unit/counit/join |
| `ChurchEncoding` | Booleans, naturals, lists, maybe, cross-type operations |
| `Limit` | Limit cones, colimit cocones, universal properties, weighted (co)limits |
| `Monad` | Monad/comonad structure types, algebras, monad from adjunction |
| `Enriched` | V-enriched category structure, V-functors, V-natural transformations |

## Documentation

- `docs/TUTORIAL.md` --- 22-section progressive tutorial covering all stdlib modules
- `docs/THEORY_CAPABILITIES.md` --- what the theory can and cannot express, with workarounds
- `docs/SURFACE_SYNTAX_CONTRACT.md` --- formal surface syntax specification
- `docs/PAPER_PARITY.md` --- paper-to-implementation traceability

## Architecture

```
src/
├── main.rs                 # Binary entry point (ditt CLI)
├── lib.rs                  # Crate root
├── api/
│   ├── foundation.rs       # All domain types (Expr, CatType, ProofTerm, etc.)
│   ├── syntax.rs           # Traits: Lexer, Parser, Formatter
│   ├── semantics.rs        # Traits: TypeChecker, Normalizer, Evaluator
│   ├── tooling.rs          # Traits: ModuleSystem, Cli, Repl, LSP
│   └── interaction.rs      # CLI/REPL/LSP data types
└── runtime/
    ├── syntax.rs           # SyntaxEngine: parsing, formatting
    ├── semantics.rs        # SemanticEngine: type checking, normalization
    └── tooling.rs          # ToolingEngine: module system, CLI, REPL, LSP
```

## Using DiTT

### CLI

```bash
ditt check stdlib/Yoneda.ditt                        # Type-check a file
ditt build stdlib/Morphism.ditt                       # Build (type-check) a file
ditt fmt stdlib/Functor.ditt                          # Format a file
ditt run --entry yoneda_forward stdlib/Yoneda.ditt    # Evaluate a definition
ditt run --normalize compose stdlib/Morphism.ditt     # Normalize a definition
ditt help                                             # All commands and options
```

Source can also be piped via stdin: `cat stdlib/Yoneda.ditt | ditt check`

Build with `cargo build --release`; the binary is `target/release/ditt`.

### REPL

```
$ ditt repl
DiTT 0.1.0 — :load <file>, :help, :quit
> :load stdlib/Yoneda.ditt
Loaded stdlib/Yoneda.ditt
> yo
λa. λx. (x →[C] a)
> transport_P
λa. λb. λf. J (λz. λp. p) [f]
> :quit
```

The REPL supports `:load <file>` to load a stdlib module (or any `.ditt` file), then any definition name can be evaluated as an expression.

### Library

DiTT is also available as a Rust library (`ditt_lang`). The test suite exercises all stdlib modules:

```bash
cargo test --test contracts_stdlib_library
```

## Building and Testing

Rust edition 2024. One dependency (`unicode-ident`).

```bash
cargo check --tests          # Type-check everything
cargo test --no-fail-fast    # Full test suite
cargo test --test <file>     # Run a specific test file
cargo clippy --tests         # Lint (must be zero warnings)
cargo fmt                    # Format
```

## Design Principles

- **The paper is the specification.** Every API surface traces to a paper rule, judgment form, or syntactic clause.
- **Directed, not symmetric.** Morphisms go one way. This is the core feature, not a limitation.
- **First-order.** Categories and predicates are fixed by the signature. No quantification over predicates or categories.
- **Judgment-oriented.** Equational reasoning is judgmental (handled by the normalizer), not propositional.
- **No effects in core language.**
