# Fettuccine: Project Architecture

## Goal

A formally verified, computable implementation of Buchberger's algorithm for computing
Gröbner bases in multivariate polynomial rings, built in Lean 4 with Mathlib.

---

## Core Types

### `CMonomial σ` — `Fettuccine/CMvPolynomial.lean`

```lean
abbrev CMonomial (σ : Type*) [DecidableEq σ] := Π₀ _ : σ, ℕ
```

A monomial with variables `σ`, represented as a finitely-supported function recording each
variable's exponent. Backed by `DFinsupp` from Mathlib. Comes with:
- `CMonomial.X i` — the variable `xᵢ`
- `CMonomial.degree`, `CMonomial.lcm`, `CMonomial.isSquarefree`
- A pointwise preorder (required by all monomial orders)

### `CMvPolynomial σ R` — `Fettuccine/CMvPolynomial.lean`

```lean
abbrev CMvPolynomial (σ : Type*) [DecidableEq σ] (R : Type*) [CommSemiring R] :=
  ⨁ _ : CMonomial σ, R
```

A multivariate polynomial, represented as a direct sum (graded by monomial). Backed by
`DirectSum` from Mathlib. Ring structure, support lemmas, and coefficient access are all
proven.

### `CMonomialOrder σ` — `Fettuccine/CMonomialOrder.lean`

```lean
structure CMonomialOrder (σ : Type*) [DecidableEq σ] where
  syn            : Type*          -- synonym type carrying the order
  acm            : AddCommMonoid syn
  lo             : LinearOrder syn
  iocam          : IsOrderedCancelAddMonoid syn
  toSyn          : CMonomial σ ≃+ syn   -- additive equivalence
  toSyn_monotone : Monotone toSyn       -- monotone on pointwise order
  wf             : WellFoundedLT syn    -- well-foundedness
```

An abstract, extensible record encoding all the required properties of a monomial order.
Three concrete orders are provided:
- `CMonomialOrder.lex` — lexicographic (any `LinearOrder σ` with `WellFoundedGT`)
- `CMonomialOrder.grlex` — graded lex (`Fettuccine/CMonomialOrder/Grlex.lean`)
- `CMonomialOrder.grevlex` — graded reverse lex (`Fettuccine/CMonomialOrder/Grevlex.lean`, requires `Finite σ`)

Leading-monomial API defined in the same file:
- `leadingMonomial ord f` — written `in[ord](f)`
- `leadingCoefficient ord f`
- `leadingTerm ord f`
- `leadingMonomial_mul` — `in[ord](f*g) = in[ord](f) + in[ord](g)` (for domains)

---

## Algorithm Layer (Formal)

### Division — `Fettuccine/Divide.lean`

```lean
def mvDivide (ord) (f g : CMvPolynomial σ R) (hg : g ≠ 0)
    : CMvPolynomial σ R × CMvPolynomial σ R  -- (quotient, remainder)
```

Standard multivariate division. Terminates by the lexicographic metric
`(ord.toSyn in[ord](f), f.support.card)`. Proven correct (`mvDivide.correct`) and
unique (`mvDivide.unique`). Extended to a list of divisors via `mvDivideₙ`.

`CMonomial.divides?` is a computable `Decidable` instance (avoids `Classical.propDecidable`)
by quantifying over the finite support.

### S-polynomial — `Fettuccine/Buchberger.lean`

```lean
def sPolynomial (ord) (f g : CMvPolynomial σ R) : CMvPolynomial σ R
  -- = (lcm / in(f)) * lc(g) * f  -  (lcm / in(g)) * lc(f) * g
  --   where lcm = CMonomial.lcm in[ord](f) in[ord](g)
```

### Gröbner Basis Predicates — `Fettuccine/Buchberger.lean`

Two characterisations are defined:

| Predicate | Meaning | Status |
|-----------|---------|--------|
| `IsGroebnerBasis ord I G` | `G ⊆ I` and `initialIdeal'(G) = initialIdeal(I)` | Mathematical definition |
| `IsGroebnerBasis₁ ord I G` | `G ⊆ I` and all S-polynomials reduce to 0 mod `G` | Computational criterion |

`buchberger` — the equivalence `IsGroebnerBasis ↔ IsGroebnerBasis₁` — is the main open
theorem (`sorry`).

### Buchberger's Algorithm — `Fettuccine/Buchberger.lean`

```lean
def buchberger_groebnerBasis (ord) (gens : List (CMvPolynomial σ R)) (maxSteps : ℕ := 512)
    : List (CMvPolynomial σ R)
```

Fuel-bounded naive Buchberger loop. Computable but slow due to `DFinsupp`/`DirectSum`
kernel evaluation (segfaults for grlex/grevlex under `#eval`).

---

## Algorithm Layer (Fast)

A second, parallel representation for efficient evaluation. Lives in `Fettuccine/Algorithm/`.

### `FMonomial` — `Fettuccine/Algorithm/MvPolynomial.lean`

```lean
abbrev FMonomial := Array ℕ   -- index i = exponent of variable i
```

Operations: `zero`, `add`, `degree`, `lcm`, `divides`, `divide`.

### `FMvPolynomial R` — `Fettuccine/Algorithm/MvPolynomial.lean`

```lean
abbrev FMvPolynomial (R : Type*) := Array (FMonomial × R)
-- sorted descending by monomial order; leading term at f[0]
```

Operations: `leadingMonomial?`, `leadingCoefficient?`, `normalize`, `add`, `sub`, `mulTerm`.

### Monomial Orders — `Fettuccine/Algorithm/MonomialOrder.lean`

```lean
namespace FMonomialOrder
def lex     : FMonomial → FMonomial → Ordering
def grlex   : FMonomial → FMonomial → Ordering
def grevlex : FMonomial → FMonomial → Ordering
```

### Division — `Fettuccine/Algorithm/Divide.lean`

```lean
def FMvPolynomial.divide (ord) (f : FMvPolynomial R) (gs : Array (FMvPolynomial R))
    (fuel : ℕ := 4096) : Array (FMvPolynomial R) × FMvPolynomial R
```

### Buchberger — `Fettuccine/Algorithm/Buchberger.lean`

```lean
def FMvPolynomial.buchberger (ord) (gens : Array (FMvPolynomial R))
    (fuel : ℕ := 2048) : Array (FMvPolynomial R)
```

Includes `sPolynomial` and Buchberger's first criterion (relatively-prime skip).

---

## Support

### Representation — `Fettuccine/Repr.lean`

Pretty-printing for `CMonomial` and `CMvPolynomial`. Polynomials are wrapped in
`CMvPolynomial.Ordered` (pairing a polynomial with its order) to enable sorted display.

### Tactic — `Fettuccine/Tactic.lean`

`groebnerBasis I ord` tactic: parses the ideal, runs `buchbergerAlgorithm`, introduces the
result as a local definition. Currently inserts `sorry` for the `IsGroebnerBasis₁` proof.

### Examples — `Fettuccine/Examples.lean`, `Fettuccine/Algorithm/Examples.lean`

Runnable demos of polynomial arithmetic, monomial order comparisons, leading-monomial
computation, and the Buchberger tactic. The algorithm-layer examples use `buchberger`
directly and can be evaluated without segfaults.

---

## Dependency Graph

```
CMvPolynomial
    └── CMonomialOrder
            ├── CMonomialOrder/Grlex
            ├── CMonomialOrder/Grevlex
            └── Divide
                    └── Buchberger
                            └── Tactic
Repr  (imports CMvPolynomial, CMonomialOrder)
Examples (imports all of the above)

Algorithm/MvPolynomial          ← FMonomial + FMvPolynomial
    └── Algorithm/MonomialOrder ← FMonomialOrder.{lex, grlex, grevlex}
    └── Algorithm/Divide        ← FMvPolynomial.divide
            └── Algorithm/Buchberger ← FMvPolynomial.{sPolynomial, buchberger}
                    └── Algorithm/Examples
```

---

## Status Summary

| Component | Computable | Proven correct | Notes |
|-----------|-----------|----------------|-------|
| Monomials (`CMonomial`) | ✓ | ✓ | |
| Polynomials (`CMvPolynomial`) | ✓ | ✓ | |
| Lex order | ✓ | ✓ | |
| Grlex order | ✓ | ✓ | |
| Grevlex order | ✓ | ✓ | Requires `Finite σ` |
| Division (`mvDivide`) | ✓ | ✓ | Correct + unique |
| S-polynomial | ✓ | — | Definition only |
| Buchberger algorithm (formal) | ✓ | ✗ | `buchberger` theorem is `sorry` |
| Tactic | ✓ (runs) | ✗ | Proof is `sorry` |
| `FMonomial` / `FMvPolynomial` | ✓ | — | Fast layer, no proofs yet |
| Fast orders (`FMonomialOrder`) | ✓ | — | No proofs yet |
| Fast division | ✓ | — | No proofs yet |
| Fast Buchberger | ✓ | — | Smoke-tested against known bases |
| Translation layer | ✗ | ✗ | Phase 5, not yet started |
