# Kernel correspondence contract

The reference is [Lean 4.34.1](https://github.com/leanprover/lean4/tree/5045d0056413266e57c625dcd7c365b10e377c52).
The Rust API accepts scoped syntax. The compatibility claim is limited to the
checked cases below. The tests use Lean's trusted `Kernel.check`,
`Kernel.whnf`, and `Kernel.isDefEq` for closed typed fixtures and
`Expr.instantiate1` for open syntax fixtures.

| Rust | Lean encoding and rule |
| --- | --- |
| `BVar(i)` | `Expr.bvar i`; zero denotes the innermost binder |
| `Sort(n)` | `Expr.sort` with zero followed by `n` level successors |
| `App(f, a)` | `Expr.app f a`; β substitutes the argument into a lambda body |
| `Lam(A, b)`, `Pi(A, b)` | `Expr.lam`, `Expr.forallE`; domain at current depth, body at depth plus one |
| `Let(A, a, b)` | `Expr.letE`; type and value at current depth, body at depth plus one; ζ substitutes the value |
| `instantiate(b, a, n)` | `b.instantiate1 a`; the body has ambient depth `n + 1` and the replacement depth `n` |
| `whnf` | Head β/ζ along the function side of applications |
| `normalize`, `def_eq` | Full β/ζ normalization and structural comparison; binder names and binder annotations are erased by the mapping |

When instantiating under `d` binders, indices below `d` are preserved, index
`d` is replaced by the argument lifted by `d`, and larger indices are
decremented. Lifting itself respects binders inside the argument.

For well-typed inputs, a successful β/ζ conversion is expected to imply Lean
kernel conversion after encoding. Lean's reverse implication requires
additional rules. The oracle contains deliberate Lean-true/Rust-false examples
for function η and proof irrelevance. Universes with parameters, level max
and imax, constants and δ, inductives and ι, projections, free variables,
quotients, and declaration or type checking are future work. In particular,
the Rust result alone does not establish that either operand is well typed.
The representation does not import or certify Lean declarations. The earlier
Nanoda-based prototype is separate from this increment.

Input scope is validated before reduction or pointer-identity shortcuts. A
step budget bounds traversal and reduction work per operation. Input and
intermediate expressions have height at most 128. Arithmetic overflow,
invalid scope, and limits return distinct errors. Pointer-identical,
well-scoped expressions can compare equal by reflexivity even when they have
no normal form. Other comparisons involving nonterminating untyped terms
can exhaust the budget.

Before expanding the supported fragment, define its expression/environment
mapping, add positive and negative cases checked by the trusted Lean API, and
record any planned directional disagreement. Type checking and declaration
admission would require their own correspondence and rejection tests.

## Evidence

- 19 Lean-generated rows: nine matching equality verdicts, two deliberate
  equality disagreements, four WHNF comparisons, and four open substitutions.
- 1,024 deterministic generated Rust cases exercise normalization idempotence,
  conversion symmetry, and agreement after β and ζ expansion.
- Negative controls exercise capture and shadowing, out-of-scope indices in
  discarded children, divergence, height limits, overflow, and shared nodes
  visited at different binder depths.
