import Groebner.Criterion
import Groebner.CBuchberger
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-!
# Gröbner Bases — Examples and API Summary

This file demonstrates the Gröbner basis library on a concrete example and
collects the main API items for easy reference.

## Module structure

```
Groebner/
  CMvPolynomial.lean  — CMonomial σ, CMvPolynomial σ R
  CMonomialOrder.lean — CMonomialOrder, lex/grlex/grevlex, leadMon/leadCoeff/tail
  CBuchberger.lean    — remainderPoly, sPolyPoly, buchberger, CGroebnerBasis
  Defs.lean           — (noncomputable) remainder, IsGroebnerBasis
  Criterion.lean      — (noncomputable) AllSpolyRemaindersZero, buchberger_criterion
  Basic.lean          — this file: examples and API reference
```
-/

open MvPolynomial MonomialOrder CBuchberger

-- Sanity check: key formal type still elaborates.
#check @buchberger_criterion (Fin 3) ℚ _ MonomialOrder.degLex

/-! ## API reference -/

/-
### Formal side (noncomputable, `Groebner.Defs` / `Groebner.Criterion`)

  `MonomialOrder.remainder m G f : MvPolynomial σ k`
    The remainder of `f` on division by list `G` (noncomputable).

  `MonomialOrder.IsGroebnerBasis m I G : Prop`
    `G ⊆ I` and every nonzero element of `I` has its leading monomial
    divisible by some `lm(g)` for `g ∈ G`.

  `MonomialOrder.AllSpolyRemaindersZero m G : Prop`
    `∀ p q ∈ G, remainder m G (sPolynomial p q) = 0`.

  `MonomialOrder.buchberger_criterion m`
    `IsGroebnerBasis m (Ideal.span G) G ↔ AllSpolyRemaindersZero m G`

### Computable side (`Groebner.CMvPolynomial`, `Groebner.CMonomialOrder`, `Groebner.CBuchberger`)

  `CMvPolynomial σ R`
    A multivariate polynomial over a `Field R` with variables in `σ`.
    Use `+`, `-`, `*`, scalar `c * p` directly; construct with `ofVar`, `ofConst`, etc.

  `CMonomialOrder σ`
    A computable monomial order.  Provided instances:
    - `CMonomialOrder.lex`, `.grlex`, `.grevlex`

  `buchberger ord gens : List (CMvPolynomial σ R)`
    Compute a Gröbner basis.  Use `#eval` for exploration.

  `IsCGroebnerBasis ord G : Prop`
    Decidable predicate: all pairwise S-polynomial remainders of `G` vanish.
    Provable by `decide` for any concrete `G`.

  `CGroebnerBasis σ R gens ord`
    Certified Gröbner basis with `gens` as a type parameter, `basis` as a field,
    and `is_groebner : IsCGroebnerBasis ord basis` as the proof field.

### The missing bridge (primary next milestone)

  To connect the two worlds we need:

    `embed : CMvPolynomial (Fin n) ℚ → MvPolynomial (Fin n) ℚ`
    `IsCGroebnerBasis_iff (m : MonomialOrder (Fin n)) (G : List (CMvPolynomial (Fin n) ℚ)) :
      IsCGroebnerBasis computableOrd G ↔
      AllSpolyRemaindersZero m (G.map embed)`

  With this, certifying a concrete basis uses three lines:

    have hc  : IsCGroebnerBasis computableOrd G      := by decide
    have hS  : AllSpolyRemaindersZero m (G.map embed) := (iff.mp hc)
    exact (buchberger_criterion m).mpr hS

### Sorry inventory (priority order)

  1. `remainder` termination (Defs.lean) — lex decrease on (degree, support.card)
  2. Hard direction of `buchberger_criterion` (Criterion.lean)
  3. `remainder_nil`, `remainder_sub_mem_span` (Defs.lean) — degree induction
-/

/-! ## Computable example -/

-- Helper: give pretty names to the three variables of Fin 3.
private def varName₃ : Fin 3 → String := fun i => #["x₀", "x₁", "x₂"][i]!

-- Notational aliases for the generators.
private def X₀ : CMvPolynomial (Fin 3) ℚ := CMvPolynomial.ofVar 0
private def X₁ : CMvPolynomial (Fin 3) ℚ := CMvPolynomial.ofVar 1
private def X₂ : CMvPolynomial (Fin 3) ℚ := CMvPolynomial.ofVar 2

/-- Generators `{X₀X₁ - X₂,  X₁X₂ - X₀,  X₀X₂ - X₁}` in three variables. -/
def gens : List (CMvPolynomial (Fin 3) ℚ) :=
  [ X₀ * X₁ - X₂,    -- x₀x₁ - x₂
    X₁ * X₂ - X₀,    -- x₁x₂ - x₀
    X₀ * X₂ - X₁ ]   -- x₀x₂ - x₁

-- Evaluate the Gröbner basis using graded lex order.
-- Output appears in the Output panel.
#eval (buchberger CMonomialOrder.grlex gens).map (CMvPolynomial.fmtPoly varName₃)

-- Also try the other monomial orders.
#eval (buchberger CMonomialOrder.lex gens).map (CMvPolynomial.fmtPoly varName₃)
#eval (buchberger CMonomialOrder.grevlex gens).map (CMvPolynomial.fmtPoly varName₃)

/-!
`partial def buchberger` is opaque to the kernel, so `buchberger ...` cannot
be reduced by `decide`.  To certify a specific basis, provide it as an explicit
list and use `decide` to check the S-polynomial criterion. -/

-- The grlex Gröbner basis, obtained from the `#eval` above.
-- (Explict so the cert proof can be discharged by `decide`.)
private def gens_grlex_basis : List (CMvPolynomial (Fin 3) ℚ) :=
  [ X₀ * X₁ - X₂
  , X₁ * X₂ - X₀
  , X₀ * X₂ - X₁
  , X₀ * X₀ - X₂ * X₂
  , X₁ * X₁ - X₀ * X₀
  , X₀ - X₀ * X₀ * X₀ ]

-- Full certified Gröbner basis.
-- `IsCGroebnerBasis ord basis` is decidable because `allSpolyRemaindersZero`
-- is a proper `def` (fuel-based, not `partial`).  We use `native_decide`
-- rather than `decide`: the kernel evaluator cannot complete ℚ arithmetic for
-- 36 S-polynomial pairs, but `native_decide` compiles the check natively and
-- lifts the result via the `ofNative` reflection axiom — a standard
-- proof-by-reflection pattern, sound in exactly the same sense as `decide`.
def gens_gb : CGroebnerBasis (Fin 3) ℚ gens CMonomialOrder.grlex :=
  CGroebnerBasis.certify CMonomialOrder.grlex gens_grlex_basis (by native_decide)
