# Fettuccine: Architecture and Design

## Executive Summary

Fettuccine implements Buchberger's algorithm for computing Gröbner bases in Lean 4, with an emphasis on **verified correctness** and **computational efficiency**.

The core challenge: polynomial operations and monomial orders in Mathlib are built on `Finsupp`, which is **noncomputable** (uses classical choice). We need to compute Gröbner bases, but existing theory is designed for reasoning, not execution.

**Solution**: A **dual-world architecture** that separates computation from reasoning:
- **Computational world** (CMvPolynomial, CMonomial, CMonomialOrder): Built on `DFinsupp`, fully executable
- **Mathematical world** (MvPolynomial from Mathlib): Classical, rich in theorems
- **Bridge** (equivalences and lifting lemmas): Connects both worlds, enabling verification

---

## Part 1: The Computability Problem

### Why Finsupp is Noncomputable

Finsupp stores finitely-supported functions using classical decidability:

1. Declared as `noncomputable theory` at file level
2. Uses `Classical.choice` throughout (e.g., `if h : ∃ (a : α), f a = b then v h.choose else 0`)
3. Requires exact support computation at operation time
4. Classical decidability instances satisfy `LinearOrder` type requirements but lack computational content

**The paradox**: Even though `LinearOrder` requires `DecidableLE`, `DecidableEq`, etc., these can be satisfied via `Classical.propDecidable`, which uses the axiom of choice—noncomputable.

### Why DFinsupp is Computable

DFinsupp takes a different approach:

1. **Computable representation**: Stores a `Multiset` of support values rather than computed `Finset`
2. **Deferred decidability**: Proof obligations are postponed until actually needed
3. **Structure preservation**: Maintains all algebraic properties (additive, multiplicative, ideals)
4. **Decidable instances that compute**: When index types are concrete (e.g., `Fin n`), `DFinsupp.Lex` provides genuinely executable comparison functions

**Key insight**: DFinsupp + explicit comparison functions = computable polynomial operations

---

## Part 2: Key Design Decisions

### Decision 1: Parallel Structure, Not Retrofitting

**Choice**: Build a parallel computable type hierarchy (`CMvPolynomial`, `CMonomial`, `CMonomialOrder`) rather than trying to make `MvPolynomial` computable.

**Why**:
- Mathlib's polynomial types are optimized for reasoning, not computation
- Retrofitting would require massive refactoring of Mathlib
- Clean separation makes it clear which code is executable
- Easy to optimize computable versions independently

**Trade-off**: Code duplication in definitions, but reusable theorems through equivalences.

### Decision 2: DFinsupp for Monomials and Polynomials

**Choice**:
- `CMonomial σ` = `Π₀ i : σ, ℕ` (DFinsupp of exponents)
- `CMvPolynomial σ R` = `⨁ m : CMonomial σ, R` (DirectSum of coefficients indexed by monomials)

**Why**:
- Preserves sparsity (no unnecessary zero coefficients)
- DFinsupp operations are computable when index types are concrete
- Avoids Finsupp's classical decidability

### Decision 3: Require DecidableEq on Index Types

**Choice**: All computable types require `[DecidableEq σ]` on the variable type.

**Effect**:
- ✅ Computable for: `Fin n`, `ℕ`, `ℤ`, concrete types
- ❌ Not computable for: abstract or infinite types without decidability

**Benefit**: Creates a clear contract—computable structures require decidable types.

### Decision 4: Explicit Comparison Functions

**Choice**: Instead of relying on classical `LinearOrder` instances, implement explicit comparison functions:
```lean
def cmpLex (m₁ m₂ : CMonomial σ) : Ordering := ...
```

**Why**:
- Comparison functions are inherently computable
- Can be evaluated directly with `#eval`
- Avoid dependence on classical decidability
- Easy to specify and verify multiple monomial orders (lex, grlex, grevlex)

---

## Part 3: The Computation → Reasoning Bridge

### Equivalence Strategy

Mathlib provides proven equivalences between `Finsupp` and `DFinsupp`:

```lean
finsuppAddEquivDFinsupp : (σ →₀ ℕ) ≃+ (Π₀ i : σ, ℕ)
```

This is a **structure-preserving isomorphism** that:
- Preserves function values
- Preserves support sets
- Preserves all arithmetic operations
- Forms mutual inverses

### Lifting Theorems

Given a theorem about Finsupp-based polynomials, transfer it to computable versions:

```
Classical theorem (Finsupp-based)
        ↓ (via equivalence)
Computable equivalent (proven to hold)
        ↓ (implementation)
Executable code
```

**Pattern**:
1. Convert computable objects to classical Finsupp via equivalence
2. Apply classical theorem
3. Convert back, preserving the equality

### Buchberger's Proof Strategy

**Key insight**: Construct the proof certificate **during computation**, not after.

```
1. Compute basis + proof that all S-polynomials reduce to zero (computable)
         ↓
2. Lift basis to MvPolynomial (straightforward embedding)
         ↓
3. Apply Buchberger's theorem (classical, no computation needed)
         ↓
Result: IsGroebnerBasis (proven and backed by computation)
```

This works because:
- Buchberger's criterion (S-polys reduce to zero ⟹ Gröbner basis) is a classical theorem
- We do the computational work (verifying reductions) and capture it as a proof certificate
- The final proof is classical but grounded in executable verification

---

## Part 4: Architecture Components

### Layer 1: Computation (Fully Executable)

**Files**: `CMvPolynomial.lean`, `CMonomialOrder.lean`, `Divide.lean`, `Buchberger.lean`

- `CMonomial σ`: Monomials as DFinsupp
- `CMvPolynomial σ R`: Polynomials as DirectSum indexed by monomials
- `CMonomialOrder σ`: Decidable, well-founded monomial orders (lex, grlex, etc.)
- `monomial_divide`, `polynomial_divide`: Explicit division algorithms
- `buchberger_with_proof`: Computable Gröbner basis algorithm returning basis + proof certificate

**Properties**:
- ✅ No `noncomputable` markers in main definitions
- ✅ Can use `#eval` and `decide` directly
- ✅ Extractable to executable code

### Layer 2: Reasoning (Classical, Rich in Theory)

**Source**: Mathlib

- `MvPolynomial σ R`: Polymomials (noncomputable but rich theory)
- `MonomialOrder σ`: Classical monomial orders
- `IsGroebnerBasis`: Classical definition of Gröbner basis
- Membership lemmas, ideal properties, etc.

### Layer 3: Bridge (Equivalences and Lifting)

**Files**: `Lift.lean`, `BuchbergerTheorem.lean` (new files)

- `CMvPolynomial.toMvPolynomial`: Embedding of computable to classical
- `CMonomial.toMonomial`: Embedding of computable monomial to classical
- `lift_basis`: Lifts a computable basis to classical
- `buchberger_correct`: Theorem connecting computable algorithm to classical Gröbner basis property

**Properties**:
- May be `noncomputable` (reasoning-only)
- Prove that computations respect classical theory
- Enable using Mathlib theorems to reason about computed results

---

## Part 5: Decidability vs Computability (Crucial Distinction)

### Key Concept

In Lean's type system:
- **Decidable** (type-level requirement): "There exists a function that decides this"
- **Computable** (implementation-level property): "We can actually execute that function"

**Decidable instances can be classical**: `Classical.propDecidable` satisfies the type requirement but uses choice, making definitions that depend on it `noncomputable`.

### For Monomial Orders

Finsupp-based `MonomialOrder`:
- Satisfies the type requirement: has `DecidableLE`, `DecidableEq`, `DecidableLT` (via classical instances)
- Cannot be computed: any definition using these instances must be `noncomputable`
- Reason: Comparison might involve arbitrary index types without constructive decidability

DFinsupp-based `CMonomialOrder` (with concrete index types):
- Satisfies the type requirement: has `DecidableLE`, `DecidableEq`, `DecidableLT` (via DFinsupp.Lex)
- **Can be computed**: DFinsupp instances are constructive for concrete types like `Fin n`
- Reason: Limited to finite, decidable index types

### Implementation Consequence

When implementing operations:

```lean
-- Computable (explicit algorithm)
def polynomial_divide (p q : CMvPolynomial σ R) : CPoly σ R × CPoly σ R :=
  ... (recursive algorithm that terminates)

-- Classical (existence theorem)
theorem polynomial_divide_exists (p q : MvPolynomial σ R) :
    ∃ (quot rem : MvPolynomial σ R), ... := by
  ... (uses choice, tactics, lemmas)
```

---

## Part 6: Operation Semantics

### Polynomial Division

**Dual implementation**:

1. **Computable** (`polynomial_divide` on `CMvPolynomial`):
   - Directly computable algorithm: reduce leading terms
   - Returns quotient and remainder
   - Fully executable

2. **Classical** (lifted via equivalence):
   - Proves that computable division is correct
   - Connects to Mathlib's division theory
   - Enables reasoning about computed results

### Monomial Comparison

**Two implementations**:

1. **Computable** (explicit function):
   ```lean
   def cmp_lex (m₁ m₂ : CMonomial σ) : Ordering := ...
   ```
   - Executable algorithm
   - Used in polynomial operations
   - Defines the order operationally

2. **Classical** (theorem):
   ```lean
   theorem cmp_lex_spec : cmp_lex m₁ m₂ = .lt ↔ m₁ < m₂ := ...
   ```
   - Proves correctness of computable comparison
   - Connects to classical order theory
   - Enables proving properties of algorithms

### Buchberger's Algorithm

**Execution model**:
- Pure function: `buchberger_with_proof : CMonomialOrder σ → Finset (CMvPolynomial σ R) → Σ basis, AllSPolyReduce basis`
- Returns: basis + proof certificate (all S-polynomials reduce to zero internally)
- Fully computable: use `#eval` on concrete examples

**Verification model**:
- Classical theorem: `buchberger_correct : IsGroebnerBasis (lift_basis (buchberger ...).val)`
- Proof uses: certificate + Buchberger's theorem + lifting equivalences
- No computation needed in proof

---

## Part 7: The Complete Picture

```
User's Problem: Compute/prove Gröbner bases
       ↓
Computation Layer (CMvPolynomial, explicit algorithms)
  - polynomial_divide : executable
  - buchberger_with_proof : executable
  - generates proof certificates during execution
       ↓
Lifting Layer (embedding + equivalences)
  - toMvPolynomial : converts computable to classical
  - Proves computation respects structure
       ↓
Reasoning Layer (Mathlib theorems)
  - Buchberger's theorem: S-polys reduce ⟹ Gröbner
  - Ideal membership lemmas: use basis to prove membership
  - Radical membership: analyze basis structure
       ↓
Result:
  - Computed basis (from #eval)
  - Verified proof that it's Gröbner (by theorem)
  - Can use basis for further reasoning
```

---

## Part 8: Design Advantages

1. **Separation of concerns**: Computation separate from reasoning
2. **Clear executability**: Type system shows what can run
3. **Flexible optimization**: Can optimize computable versions without affecting proofs
4. **Reuse of Mathlib**: Leverage vast classical theory via equivalences
5. **Gradual verification**: Can test algorithms before proving every detail
6. **Educational value**: Makes algorithms explicit and inspectable

---

## References

- [DFinsupp.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/DFinsupp/Defs.html) — Computable finitely-supported functions
- [Finsupp.ToDFinsupp](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finsupp/ToDFinsupp.html) — Equivalence between Finsupp and DFinsupp
- [DFinsupp.Lex](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/DFinsupp/Lex.html) — Decidable lexicographic ordering on DFinsupp
- [Mathlib Polynomial Operations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Basic.html)
- [Theorem Proving in Lean 4 - Axioms and Computation](https://lean-lang.org/theorem_proving_in_lean4/axioms_and_computation.html)
