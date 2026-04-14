# Fettuccine: Implementation Phases

## Overview

This document consolidates the phased approach for implementing Buchberger's algorithm. The path is strictly sequential—later phases depend on earlier foundations.

---

## Phase 1: Complete Foundation (Prerequisite)

### Objectives
- Prepare existing infrastructure for building algorithms
- Uncomment and stabilize leading monomial lemmas
- Implement basic polynomial division
- Complete missing monomial orders

### Timeline
~250 lines of code + uncommenting, ~2-3 days

### Deliverables

#### 1.1 Uncomment Leading Monomial Lemmas (CMonomialOrder.lean, lines 218–262)
**Files**: `Fettuccine/CMonomialOrder.lean`

**Tasks**:
- [ ] Uncomment `leadingMonomial_mem_support`
- [ ] Uncomment `le_leadingMonomial` and related inequalities
- [ ] Uncomment `leadingMonomial_mul` and multiplicative properties
- [ ] Uncomment `leadingCoefficient` lemmas
- [ ] Verify all proofs compile
- [ ] Update Examples to show leading monomial operations

**Success Criteria**:
- All lemmas prove without errors
- Examples in Examples.lean compile and produce expected output
- No performance regressions

#### 1.2 Implement Polynomial Division (Divide.lean)
**Files**: `Fettuccine/Divide.lean` (currently empty)

**Tasks**:
- [ ] Implement `monomial_divide : CMonomial σ → CMonomial σ → Option (CMonomial σ)`
  - Returns `some (m₁ - m₂)` if m₂ divides m₁ (all exponents of m₂ ≤ m₁)
  - Returns `none` otherwise
  - Must be decidable (can use `decide` tactic)

- [ ] Prove `monomial_divide_spec`: Characterizes when division succeeds
  ```lean
  theorem monomial_divide_spec (m₁ m₂ : CMonomial σ) :
      (monomial_divide m₁ m₂).isSome ↔ (∀ i, m₂ i ≤ m₁ i)
  ```

- [ ] Implement `polynomial_reduce_step : CMvPolynomial σ R → CMvPolynomial σ R → CMvPolynomial σ R`
  - Single reduction step: if LT(f) is divisible by LT(g), subtract scaled g
  - Returns updated polynomial (or original if no reduction possible)

- [ ] Implement `polynomial_reduce : CMvPolynomial σ R → CMvPolynomial σ R → CMvPolynomial σ R`
  - Loop: repeatedly reduce until leading term no longer divisible
  - Proof: uses well-founded recursion on monomial order
  - Theorem: `polynomial_reduce_span` — reduced polynomial in same ideal as original

**Code Sketch**:
```lean
def monomial_divide (m₁ m₂ : CMonomial σ) : Option (CMonomial σ) :=
  if h : ∀ i, m₂ i ≤ m₁ i then
    some ⟨fun i => m₁ i - m₂ i⟩
  else
    none

def polynomial_reduce (f g : CMvPolynomial σ R) (ord : CMonomialOrder σ) :
    CMvPolynomial σ R :=
  let ⟨m_f, c_f⟩ := f.leadingTerm
  let ⟨m_g, c_g⟩ := g.leadingTerm
  match monomial_divide m_f m_g with
  | some m => polynomial_reduce (f - C (c_f / c_g) * (X_monomial m) * g) g ord
  | none => f
```

**Success Criteria**:
- `monomial_divide` compiles and is clearly decidable
- `polynomial_reduce` terminates (can use `decide` on concrete examples)
- Examples: divide x² + 1 by x + 1 produces correct quotient and remainder
- Division theorem compiles without sorries

#### 1.3 Complete Graded Monomial Orders (CMonomialOrder.lean)
**Files**: `Fettuccine/CMonomialOrder.lean`

**Tasks**:
- [ ] Uncomment `grlex` implementation (lines 149–161)
- [ ] Fix any compilation errors in `grlex` definition
- [ ] Implement `grevlex` (graded reverse lexicographic) from scratch
  - Lexicographic comparison on reversed exponent vectors
  - Use similar structure to grlex

- [ ] Prove order properties:
  ```lean
  theorem grlex_wellFounded : WellFoundedLT (CMonomial σ) := ...
  theorem grlex_translation_invariant : ... := ...
  ```

- [ ] Add Examples:
  - Compare monomials under grlex
  - Verify grlex respects total degree
  - Show difference between grlex and grevlex

**Success Criteria**:
- `grlex` and `grevlex` are no longer stubs
- All order axioms proved (well-founded, translation-invariant, monotone)
- Examples show correct ordering behavior
- No regressions in existing lex examples

### Risk Areas
1. **Proof effort**: Leading monomial lemmas may require technique refinements. Estimate ~20 lines per lemma.
2. **Termination**: Polynomial reduction must prove termination via monomial order well-foundedness. Use explicit measure if needed.
3. **Type class inference**: Division algorithm needs `DecidableEq R` for coefficient operations. May need explicit instances in examples.

### Dependencies
- None (Phase 1 is foundational)

### Success Metrics
- [ ] All new code compiles without `sorry`
- [ ] `#eval` examples show correct polynomial division
- [ ] Examples.lean has new section demonstrating division and new monomial orders
- [ ] CI/tests pass (if any exist)

---

## Phase 2: S-Polynomials and Reduction (Core Algorithm)

### Objectives
- Implement S-polynomial computation
- Implement the reduction procedure
- Prove key lemmas connecting to ideal membership

### Timeline
~100-150 lines of code, ~3 days

### Deliverables

#### 2.1 Monomial LCM and S-Polynomials
**Files**: New file `Fettuccine/SPoly.lean` or extend `Fettuccine/CMonomialOrder.lean`

**Tasks**:
- [ ] Implement `lcm_monomial : CMonomial σ → CMonomial σ → CMonomial σ`
  ```lean
  def lcm_monomial (m₁ m₂ : CMonomial σ) : CMonomial σ :=
    ⟨fun i => max (m₁ i) (m₂ i)⟩
  ```

- [ ] Prove `lcm_monomial_properties`:
  ```lean
  theorem lcm_spec (m₁ m₂ m : CMonomial σ) :
      m₁ ∣ m ∧ m₂ ∣ m ↔ lcm_monomial m₁ m₂ ∣ m := ...
  ```

- [ ] Implement `S_poly : CMvPolynomial σ R → CMvPolynomial σ R → CMvPolynomial σ R`
  ```lean
  def S_poly (f g : CMvPolynomial σ R) : CMvPolynomial σ R :=
    let m := lcm_monomial (f.leadingMonomial) (g.leadingMonomial)
    let cf := f.leadingCoeff
    let cg := g.leadingCoeff
    (m / f.leadingMonomial) * f - (m / g.leadingMonomial) * g
  ```
  - Handle zero cases carefully
  - Result should be 0 or have strictly smaller leading term than f or g

- [ ] Prove `S_poly_membership`:
  ```lean
  theorem S_poly_in_ideal (f g : CMvPolynomial σ R) :
      S_poly f g ∈ Ideal.span {f, g} := ...
  ```

#### 2.2 Full Reduction Procedure
**Files**: `Fettuccine/SPoly.lean` or `Fettuccine/Divide.lean`

**Tasks**:
- [ ] Implement `reduce_by : CMvPolynomial σ R → Finset (CMvPolynomial σ R) → CMvPolynomial σ R`
  ```lean
  def reduce_by (f : CMvPolynomial σ R) (basis : Finset (CMvPolynomial σ R)) :
      CMvPolynomial σ R :=
    f.foldl (fun acc g =>
      if g ≠ 0 ∧ (g.leadingMonomial ∣ acc.leadingMonomial) then
        polynomial_reduce_step acc g
      else
        acc) f
  ```
  - Takes polynomial f and list of basis polynomials
  - Repeatedly reduces f against basis elements
  - Terminates when no basis element divides leading term of remainder

- [ ] Prove `reduce_by_properties`:
  ```lean
  theorem reduce_by_span (f : CMvPolynomial σ R) (basis : Finset (CMvPolynomial σ R)) :
      f - reduce_by f basis ∈ Ideal.span basis := ...
  ```
  - This says: remainder equals f minus something in the ideal

- [ ] Theorem about zero reduction and ideal membership:
  ```lean
  theorem reduce_by_zero_iff_ideal_member (f : CMvPolynomial σ R)
      (basis : Finset (CMvPolynomial σ R)) (hbasis : IsGroebnerBasis basis) :
      reduce_by f basis = 0 ↔ f ∈ Ideal.span basis := ...
  ```

#### 2.3 Examples and Verification
**Files**: `Fettuccine/Examples.lean`

**Tasks**:
- [ ] Example: S-polynomial of x² - 1 and x - 1 (should reduce to 0)
- [ ] Example: Reduction of x³ - 1 by {x - 1, x² + x + 1}
- [ ] Demonstrate that non-Gröbner basis has non-zero S-polynomial reductions

### Risk Areas
1. **S-polynomial coefficient arithmetic**: Dividing by leading coefficients in non-field rings is tricky. Restrict to fields first, generalize later.
2. **Reduction termination**: Needs careful proof that monomial order is decreasing. Use explicit measure if needed.

### Dependencies
- Phase 1 (monomial division, leading monomial lemmas)

### Success Metrics
- [ ] S-polynomials compile and compute correctly on examples
- [ ] Reduction procedure terminates on all test cases
- [ ] `#eval reduce_by S_poly_example basis` produces 0 when expected
- [ ] Zero-reduction lemma proves without sorries

---

## Phase 3: Buchberger's Algorithm with Certificate

### Objectives
- Implement the core Buchberger loop
- Generate proof certificate during execution
- Connect to classical theory via lifting

### Timeline
~100-150 lines of code, ~4-5 days

### Deliverables

#### 3.1 Proof Certificate Definition
**Files**: New file `Fettuccine/Buchberger.lean`

**Tasks**:
- [ ] Define `AllSPolyReduce : CMonomialOrder σ → Finset (CMvPolynomial σ R) → Prop`
  ```lean
  def AllSPolyReduce (ord : CMonomialOrder σ) (basis : Finset (CMvPolynomial σ R)) : Prop :=
    ∀ f g ∈ basis, reduce_by (S_poly f g) basis = 0
  ```
  - This is the property we'll capture during computation

#### 3.2 Buchberger Loop with Proof Collection
**Files**: `Fettuccine/Buchberger.lean`

**Tasks**:
- [ ] Implement `buchberger_with_proof`:
  ```lean
  def buchberger_with_proof (ord : CMonomialOrder σ) (gens : Finset (CMvPolynomial σ R)) :
      Σ (basis : Finset (CMvPolynomial σ R)), AllSPolyReduce ord basis := by
    -- Tail-recursive loop
    -- State: (current_basis, pairs_to_check)
    -- Invariant: For all checked pairs, S-poly reduces to 0
    -- Loop body:
    --   1. Pick (f, g) from pairs_to_check
    --   2. Compute r := reduce_by (S_poly f g) current_basis
    --   3. If r = 0:
    --       Record that this pair reduces to zero
    --       Continue to next pair
    --   4. If r ≠ 0:
    --       Add r to basis
    --       Generate new pairs involving r
    --       Recur with expanded basis
    -- Termination: Uses well-founded measure on set of pairs
  ```

- [ ] Implement `buchberger_loop` helper:
  ```lean
  def buchberger_loop (basis : Finset (CMvPolynomial σ R))
      (pairs : Finset (CMvPolynomial σ R × CMvPolynomial σ R))
      (checked : ∀ (f g ∈ pairs), ...) : -- proof that checked pairs reduce
      Σ (basis' : Finset (CMvPolynomial σ R)), AllSPolyReduce basis' := ...
  ```

- [ ] Termination proof:
  - Use well-founded recursion on set of pairs
  - Or use fuel-based recursion with concrete bounds
  - Should be able to verify termination on small examples with `#eval`

#### 3.3 Correctness Theorem
**Files**: `Fettuccine/Buchberger.lean`

**Tasks**:
- [ ] Prove `buchberger_generates_ideal`:
  ```lean
  theorem buchberger_generates_ideal (ord : CMonomialOrder σ) (gens : Finset (CMvPolynomial σ R)) :
      Ideal.span (buchberger_with_proof ord gens).val.val = Ideal.span gens := ...
  ```
  - Proof: Reductions don't add anything new to the ideal

#### 3.4 Examples
**Files**: `Fettuccine/Examples.lean`

**Tasks**:
- [ ] Example 1: Ideal ⟨x² - 1, x - 1⟩ over field
  ```lean
  #eval (buchberger_with_proof lex {x² - 1, x - 1}).val
  ```
  Should return: {x - 1}

- [ ] Example 2: More complex ideal, verify S-polynomials reduce

### Risk Areas
1. **Fuel-based recursion**: May need explicit fuel bound. Check termination on examples.
2. **Proof certificate generation**: Must ensure we actually build the certificate during loop, not as afterthought.
3. **Pair selection strategy**: Algorithm choice (all pairs vs. Buchberger's criterion) affects performance. Implement simple version first.

### Dependencies
- Phase 1 (division, monomial orders)
- Phase 2 (S-polynomials, reduction)

### Success Metrics
- [ ] `buchberger_with_proof` compiles and is marked `computable` (or has computable definition)
- [ ] `#eval` produces basis on small examples
- [ ] Termination verified on 2-3 test cases
- [ ] Generated certificate is non-trivial (not just `trivial`)
- [ ] `buchberger_generates_ideal` theorem compiles

---

## Phase 4: Classical Theorems and Lifting

### Objectives
- State and prove Buchberger's classical theorem
- Implement lifting from CMvPolynomial to MvPolynomial
- Connect computation to classical Gröbner basis property

### Timeline
~150-200 lines of code, ~4-5 days

### Deliverables

#### 4.1 Lifting Definitions
**Files**: New file `Fettuccine/Lift.lean`

**Tasks**:
- [ ] Define `lift_monomial : CMonomial σ → MvPolynomial σ ℕ`
  - Map to function-style representation or standard Mathlib representation

- [ ] Define `lift_poly : CMvPolynomial σ R → MvPolynomial σ R`
  - Preserve all algebraic structure

- [ ] Prove `lift_preserves_span`:
  ```lean
  theorem lift_preserves_span (gens : Finset (CMvPolynomial σ R)) :
      Ideal.span (gens.image lift_poly : Set (MvPolynomial σ R)) =
      Ideal.span (gens.map lift_poly) := ...
  ```

- [ ] Prove `lift_injective`:
  ```lean
  theorem lift_injective : Function.Injective lift_poly := ...
  ```

#### 4.2 Buchberger's Classical Theorem
**Files**: `Fettuccine/Lift.lean`

**Tasks**:
- [ ] State `buchberger_criterion`:
  ```lean
  theorem buchberger_criterion (basis : Finset (MvPolynomial σ R)) (ord : CMonomialOrder σ) :
      (∀ f g ∈ basis, reduce_by_mv (S_poly_mv f g) basis = 0) →
      IsGroebnerBasis ord basis := ...
  ```
  - This is a classical statement, proven via classical reasoning
  - May need to use existing Mathlib lemmas (if they exist) or prove from first principles

- [ ] Prove `reduce_by_mv_spec`:
  ```lean
  theorem reduce_by_mv_spec (f : MvPolynomial σ R) (basis : Finset (MvPolynomial σ R)) :
      f - reduce_by_mv f basis ∈ Ideal.span basis := ...
  ```

#### 4.3 Main Lifting Theorem
**Files**: `Fettuccine/Lift.lean`

**Tasks**:
- [ ] Theorem `buchberger_correct`:
  ```lean
  theorem buchberger_correct (ord : CMonomialOrder σ) (gens : Finset (CMvPolynomial σ R)) :
      let ⟨basis, cert⟩ := buchberger_with_proof ord gens
      IsGroebnerBasis ord (basis.image lift_poly) := by
    -- Unfold cert : AllSPolyReduce ord basis
    -- Convert to reduce_by_mv via lift
    -- Apply buchberger_criterion
    ...
  ```

- [ ] Additional theorem for ideal equality:
  ```lean
  theorem buchberger_ideal_eq (ord : CMonomialOrder σ) (gens : Finset (CMvPolynomial σ R)) :
      Ideal.span (gens.image lift_poly) =
      Ideal.span ((buchberger_with_proof ord gens).val.image lift_poly) := ...
  ```

#### 4.4 Examples and Verification
**Files**: `Fettuccine/Examples.lean`

**Tasks**:
- [ ] Example: Compute basis, apply theorem, conclude it's Gröbner
- [ ] Example: Use basis property to prove membership of specific polynomial
- [ ] Show complete proof workflow: compute → lift → apply theorem → use result

### Risk Areas
1. **Buchberger's theorem proof**: If Mathlib doesn't have a ready theorem, this could be substantial. May be a good point to consult or reference the literature.
2. **Lifting correctness**: Must ensure lifting preserves all operational semantics exactly.

### Dependencies
- Phase 1-3 (all computation phases)
- Mathlib theorems (may need to check availability)

### Success Metrics
- [ ] Lifting functions compile and are proven correct
- [ ] `buchberger_criterion` theorem statement compiles
- [ ] `buchberger_correct` theorem compiles without `sorry`
- [ ] Examples show complete flow from computation to proven result

---

## Phase 5: Tactic Layer and Polish

### Objectives
- Wrap algorithm in convenient tactic interface
- Create comprehensive examples
- Documentation and cleanup

### Timeline
~50 lines of code + docs, ~2-3 days

### Deliverables

#### 5.1 Groebner Basis Tactic
**Files**: New file `Fettuccine/Tactic.lean`

**Tasks**:
- [ ] Implement `groebner_basis` tactic:
  ```lean
  tactic groebner_basis (ord : CMonomialOrder σ) (gens : Finset (CMvPolynomial σ R)) : Unit :=
    -- Compute basis using buchberger_with_proof
    -- Populate context with:
    --   1. Definition: gb_basis := (buchberger_with_proof ord gens).val.image lift_poly
    --   2. Proof: gb_is_groebner : IsGroebnerBasis ord gb_basis
    -- User can now reference these in subsequent tactics
  ```

- [ ] Optional: `groebner_basis_ideal` variant for abstract ideals
  - Extract generators from `Ideal (MvPolynomial σ R)`
  - Run buchberger
  - Prove ideal equality

#### 5.2 Comprehensive Examples
**Files**: `Fettuccine/Examples.lean`

**Tasks**:
- [ ] Example showing full workflow:
  ```lean
  example : some_polynomial_property := by
    groebner_basis lex {f₁, f₂, f₃}
    -- gb_basis is now in context
    -- gb_is_groebner is available to use
    ...
  ```

- [ ] Examples from literature (if any)
- [ ] Performance demonstration on interesting examples

#### 5.3 Documentation
**Files**: Updates to inline documentation, new `EXAMPLE-USAGE.md`

**Tasks**:
- [ ] Add docstrings to all public definitions
- [ ] Create quick-start guide
- [ ] Document limitations (finite variables, decidability requirements)
- [ ] Add references to theory

### Dependencies
- Phase 1-4 (all prior work)

### Success Metrics
- [ ] Tactic compiles and works on examples
- [ ] Examples.lean demonstrates complete usage
- [ ] Documentation is clear and accessible
- [ ] Project is release-ready

---

## Critical Path Summary

```
Start
  ↓
Phase 1: Foundation (polynomial division, lemmas, orders)
  ↓
Phase 2: S-polynomials & reduction
  ↓
Phase 3: Buchberger loop with certificate
  ↓
Phase 4: Classical theorems & lifting
  ↓
Phase 5: Tactic & polish
  ↓
Release
```

**No parallelization possible**: Each phase strictly depends on the prior one.

---

## Effort and Risk Summary

| Phase | Effort | Lines | Risk | Days |
|-------|--------|-------|------|------|
| 1 | Low | 250 | Low-Medium | 2-3 |
| 2 | Medium | 150 | Medium | 3 |
| 3 | Medium-High | 150 | High (termination) | 4-5 |
| 4 | Medium | 200 | Medium-High (lift validity) | 4-5 |
| 5 | Low | 50 | Low | 2-3 |
| **Total** | **High** | **~800** | **Medium** | **15-19** |

---

## Success Metrics (Global)

By end of Phase 5, Fettuccine should:

- ✅ Compute Gröbner bases for polynomial systems with 2-4 variables and degree ≤ 10
- ✅ Use `#eval` to compute bases on concrete examples
- ✅ Provide tactic that populates context with computed basis and proof
- ✅ All core definitions are marked computable (not `noncomputable`)
- ✅ Proofs of correctness compile and are self-contained
- ✅ Examples demonstrate complete workflows
- ✅ Documentation explains architecture and usage

---

## Known Limitations and Future Work

### Current Scope
- Finite variable sets (Fin n or Fintype)
- Decidable coefficient rings (ℚ, ZMod p)
- Buchberger's algorithm (no advanced heuristics)

### Future Enhancements
1. **Optimizations**: Buchberger's criterion for pair selection, sugar strategy
2. **Infinite variables**: Support for ℕ-indexed variables
3. **Advanced theory**: Radical membership, elimination ideals
4. **Extraction**: Generate runnable code from verified algorithm
5. **Integration**: Connect with CoqPoly or other verification projects

---

## References

- [Buchberger's Algorithm](https://en.wikipedia.org/wiki/Buchberger%27s_algorithm) — Wikipedia overview
- [Gröbner Bases and Applications](https://www.springer.com/gp/book/9780387981925) — Cox, Little, O'Shea
- Mathlib documentation for polynomial and ideal theory
- Previous research documents: ARCHITECTURE-AND-DESIGN.md, dfinsupp-computability.md
