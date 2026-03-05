/-
# Gröbner Bases — Examples and API Summary

This file demonstrates the Gröbner basis library on concrete examples and collects
the main API theorems for easy reference.

## Module structure

```
Groebner/
  Defs.lean       — remainder, IsGroebnerBasis, LmDvd
  Criterion.lean  — AllSpolyRemaindersZero, buchberger_criterion
  Algorithm.lean  — buchbergerLoop, buchberger, buchberger_isGroebnerBasis
  Basic.lean      — this file: examples and overview
```

## Notes on verified vs. verifying

The project supports two workflows:

**Verified algorithm** (`buchberger`): run the algorithm and obtain a provably correct
Gröbner basis via `buchberger_isGroebnerBasis`.  The result is *some* Gröbner basis
(non-deterministically chosen via `Classical.choose`); it may differ from the specific
list produced by a CAS.

**Verifying checker** (`AllSpolyRemaindersZero` + `buchberger_criterion`): given a
*specific* candidate basis `G` (computed externally), prove `AllSpolyRemaindersZero m G`
and apply `buchberger_criterion.mpr`.  Once `sorry`s are closed, this can be closed by
`native_decide` for concrete polynomial rings.

## Example

The ideal `I = ⟨f₁, f₂⟩` where `f₁ = x₀x₁ - x₂x₃` and `f₂ = -x₁² + x₀x₂` in
`ℚ[x₀,x₁,x₂,x₃]` under the degree-lex order has Gröbner basis that additionally includes
the polynomial `f₃ = -x₁x₂x₃ + x₀²x₂`.
-/

import Groebner.Algorithm
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

open MvPolynomial MonomialOrder

/-! ## Concrete polynomial ring setup -/

/-- Variables indexed by `Fin 4`: four indeterminates `x₀, x₁, x₂, x₃`. -/
abbrev Vars := Fin 4

/-- The ambient polynomial ring `ℚ[x₀, x₁, x₂, x₃]`. -/
abbrev P := MvPolynomial Vars ℚ

/-- Degree-lex monomial order on four variables. -/
noncomputable def dlex : MonomialOrder Vars :=
  (MonomialOrder.degLex : MonomialOrder (Fin 4))

/-- Variable shorthand: `xᵢ = X i`. -/
noncomputable def xv (i : Vars) : P := X i

/-! ## Input generators -/

/-- `f₁ = x₀ · x₁ - x₂ · x₃` -/
noncomputable def f₁ : P := xv 0 * xv 1 - xv 2 * xv 3

/-- `f₂ = -x₁² + x₀ · x₂` -/
noncomputable def f₂ : P := -(xv 1) ^ 2 + xv 0 * xv 2

/-- `f₃ = -x₁ · x₂ · x₃ + x₀² · x₂` — the expected additional Gröbner element. -/
noncomputable def f₃ : P := -(xv 1 * xv 2 * xv 3) + xv 0 ^ 2 * xv 2

/-- Input generators list. -/
noncomputable def genList : List P := [f₁, f₂]

/-- The ideal `I = ⟨f₁, f₂⟩`. -/
noncomputable def I : Ideal P := Ideal.span { g | g ∈ genList }

/-! ## Using the verified algorithm -/

/-- The output of Buchberger's algorithm on our generators forms *some* Gröbner basis for `I`.

Note: the exact list is non-deterministic (depends on `Classical.choose` choices in
`remainder`), but the correctness theorem holds regardless. -/
theorem buchberger_output_correctness :
    IsGroebnerBasis dlex I (buchberger dlex genList) := by
  -- I = Ideal.span { g | g ∈ genList } by definition
  exact buchberger_isGroebnerBasis dlex genList

/-! ## Using the verifying checker -/

/-- Claimed Gröbner basis (computed by a CAS such as SageMath). -/
noncomputable def claimedBasis : List P := [f₁, f₂, f₃]

/-- The claimed basis spans the same ideal `I` as the generators.
Proof deferred (requires checking f₃ ∈ I and gens ⊆ claimedBasis). -/
theorem claimedBasis_span : Ideal.span { g | g ∈ claimedBasis } = I := by
  sorry

/-- All S-polynomial remainders for the claimed basis vanish.
TODO: close with `native_decide` once `remainder` is computable. -/
theorem claimedBasis_allSPolyZero : AllSpolyRemaindersZero dlex claimedBasis := by
  sorry

/-- `claimedBasis` is a Gröbner basis for `I`. -/
theorem claimedBasis_isGroebnerBasis : IsGroebnerBasis dlex I claimedBasis := by
  rw [← claimedBasis_span]
  exact (buchberger_criterion dlex).mpr claimedBasis_allSPolyZero

/-! ## Type-checking roundtrip -/

-- Sanity check: the key types elaborate correctly.
#check @buchberger_isGroebnerBasis (Fin 4) ℚ _ dlex
#check @buchberger_criterion       (Fin 4) ℚ _ dlex

/-! ## API reference -/

/-
**Key definitions** (all in the `MonomialOrder` namespace):

  `remainder m G f : MvPolynomial σ k`
    The remainder of `f` on division by list `G` (over a field).

  `IsGroebnerBasis m I G : Prop`
    `G ⊆ I` and every nonzero element of `I` has its leading monomial divisible
    by some `lm(g)` for `g ∈ G`.

  `AllSpolyRemaindersZero m G : Prop`
    `∀ p q ∈ G, remainder m G (sPolynomial p q) = 0`.

  `buchberger m gens : List (MvPolynomial σ k)`
    Computes a Gröbner basis from the generator list `gens`.

**Key theorems**:

  `buchberger_criterion m`
    `IsGroebnerBasis m (Ideal.span G) G ↔ AllSpolyRemaindersZero m G`

  `buchberger_isGroebnerBasis m gens`
    `IsGroebnerBasis m (Ideal.span gens) (buchberger m gens)`

  `buchberger_span_eq m gens`
    `Ideal.span (buchberger m gens) = Ideal.span gens`

  `remainder_sub_mem_span m G f`
    `f - remainder m G f ∈ Ideal.span G`

**Sorry inventory** (in priority order for future work):

  1. `remainder` termination   — lex order on (degree, support.card)
  2. `buchbergerLoop` termination — Dickson's Lemma / ACC on monomial ideals
  3. Hard direction of `buchberger_criterion` — sPolynomial_decomposition induction
  4. `remainder_nil`, `remainder_sub_mem_span` — degree induction
  5. `buchbergerLoop_span_eq`  — ideal invariant of the loop
  6. `buchberger_allSpolyRemaindersZero` — loop-exit invariant
-/
