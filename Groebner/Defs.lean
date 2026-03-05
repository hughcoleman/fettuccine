/-
# Core definitions for Gröbner bases

This file defines the central notions needed for Gröbner bases of polynomial ideals:

* `MonomialOrder.remainder m G f` — the remainder of `f` on division by the list `G`,
  computed by the standard multivariate division algorithm over a field.

* `MonomialOrder.IsGroebnerBasis m I G` — `G` is a Gröbner basis of ideal `I` with respect
  to the monomial order `m`.

* `MonomialOrder.LmDvd m p f` — the leading monomial of `p` divides that of `f`.

## Implementation notes

All definitions are `noncomputable` and use `Classical` for decidability.  The `remainder`
function is defined by well-founded recursion; termination is deferred via `sorry` and
follows from a lexicographic decrease on `(m.toSyn (m.degree f), f.support.card)`.

## References

* [Becker-Weispfenning1993] — Gröbner Bases: A Computational Approach to Commutative Algebra.
-/

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Span

open MvPolynomial Classical

namespace MonomialOrder

variable {σ : Type*} {k : Type*} [Field k]

/-! ### Divisibility of leading monomials -/

/-- `p` divides the leading monomial of `f` with respect to monomial order `m`:
the leading monomial of `p` is componentwise ≤ the leading monomial of `f`. -/
def LmDvd (m : MonomialOrder σ) (p f : MvPolynomial σ k) : Prop :=
  m.degree p ≤ m.degree f

/-! ### Polynomial remainder -/

/-- The remainder of `f` after reducing by the list `G` of polynomials, with respect to
monomial order `m`.  This implements the standard multivariate division algorithm over a
field (where every nonzero polynomial has a unit leading coefficient).

The algorithm proceeds as follows:
* If `f = 0`, return `0`.
* If some `b ∈ G` has `b ≠ 0` and `m.degree b ≤ m.degree f`, reduce `f` by `b`
  using `MonomialOrder.reduce` and recurse.
* Otherwise, if `f` is a nonzero constant (`m.degree f = 0`), it cannot be further
  reduced; return `f`.
* Otherwise, peel off the leading term and recurse on the tail.

**Termination**: decreasing lexicographic measure `(m.toSyn (m.degree f), f.support.card)`;
deferred via `sorry`. -/
noncomputable def remainder (m : MonomialOrder σ)
    (G : List (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    MvPolynomial σ k :=
  if f = 0 then 0
  else
    if h : ∃ b ∈ G, b ≠ 0 ∧ m.degree b ≤ m.degree f then
      -- Choose a reducer: some b ∈ G with lm(b) | lm(f).
      have hbne  : h.choose ≠ 0 :=
        h.choose_spec.2.1
      have hbunt : IsUnit (m.leadingCoeff h.choose) :=
        m.isUnit_leadingCoeff.mpr hbne
      -- Reduce f by b; degree strictly decreases.
      remainder m G (m.reduce hbunt f)
    else
      -- No reducer exists for the current leading term.
      if m.degree f = 0 then
        -- f is a nonzero constant — irreducible remainder.
        f
      else
        -- Peel off the leading term; recurse on the rest.
        m.leadingTerm f + remainder m G (m.subLTerm f)
termination_by (m.toSyn (m.degree f), f.support.card)
decreasing_by
  /- Termination proof sketch (formal proof deferred):
     • Case "reducer found, degree f ≠ 0":
         degree_reduce_lt : m.degree (m.reduce hbunt f) ≺[m] m.degree f
         so the first lex component strictly decreases.
     • Case "reducer found, degree f = 0":
         Both f and h.choose are constants; m.reduce hbunt f = 0
         (C(a) - C(a/c)·C(c) = 0), so f.support.card = 0 < f.support.card.
     • Case "no reducer, degree f ≠ 0":
         degree_sub_LTerm_lt : m.degree (m.subLTerm f) ≺[m] m.degree f. -/
  all_goals sorry

/-! ### Gröbner basis -/

/-- `G` is a Gröbner basis of the ideal `I` with respect to the monomial order `m`.
The characterisation used is:
* Every polynomial in `G` belongs to `I`.
* For every nonzero `f ∈ I`, the leading monomial of `f` is divisible by the leading
  monomial of some element of `G`. -/
def IsGroebnerBasis (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ k))
    (G : List (MvPolynomial σ k)) : Prop :=
  (∀ g ∈ G, (g : MvPolynomial σ k) ∈ I) ∧
  (∀ f : MvPolynomial σ k, f ∈ I → f ≠ 0 →
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f)

/-! ### Basic properties of `remainder` -/

@[simp]
theorem remainder_zero (m : MonomialOrder σ) (G : List (MvPolynomial σ k)) :
    remainder m G 0 = 0 := by
  simp [remainder]

/-- With an empty divisor list, the remainder is the polynomial itself.
Proof by degree-induction (deferred). -/
theorem remainder_nil (m : MonomialOrder σ) (f : MvPolynomial σ k) :
    remainder m [] f = f := by
  sorry
  -- Informal: with G = [], exists branch is vacuously false; remainder [] f
  -- unfolds to  leadingTerm f + remainder [] (subLTerm f)  if degree f ≠ 0,
  -- or  f  if degree f = 0.  By induction on degree, this sums to f.

/-- The difference `f - remainder m G f` lies in the span of `G`.
Proof by induction on the recursion structure of `remainder` (deferred). -/
theorem remainder_sub_mem_span (m : MonomialOrder σ)
    (G : List (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    f - remainder m G f ∈ Ideal.span { g | g ∈ G } := by
  sorry

/-- If `G` is a Gröbner basis of `I` and `f ∈ I`, then `remainder m G f = 0`. -/
theorem remainder_eq_zero_of_isGroebnerBasis
    (m : MonomialOrder σ)
    {I : Ideal (MvPolynomial σ k)} {G : List (MvPolynomial σ k)}
    (hG : IsGroebnerBasis m I G) {f : MvPolynomial σ k} (hf : f ∈ I) :
    remainder m G f = 0 := by
  sorry

/-- The leading monomial of a nonzero remainder is not divisible by any element of `G`. -/
theorem remainder_degree_not_reducible (m : MonomialOrder σ)
    (G : List (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    remainder m G f ≠ 0 →
      ∀ g ∈ G, g ≠ 0 → ¬(m.degree g ≤ m.degree (remainder m G f)) := by
  sorry

end MonomialOrder
