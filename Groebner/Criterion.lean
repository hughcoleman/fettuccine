/-
# Buchberger's Criterion

This file states and proves (modulo `sorry`s for the hard direction) **Buchberger's
criterion**, which gives an algorithmic test for whether a finite list is a Gröbner basis.

## Main result

`MonomialOrder.buchberger_criterion` : A list `G` is a Gröbner basis for `Ideal.span G`
if and only if for every pair `(p, q)` of elements of `G`, the remainder of the
S-polynomial `S(p, q)` modulo `G` is zero.

## Strategy

The **easy direction** (Gröbner basis → all S-polynomial remainders vanish) is a standard
consequence of the definitions: `S(p, q) ∈ I` since it is a linear combination of `p` and
`q`, so `remainder G (S p q) = 0` by `remainder_eq_zero_of_isGroebnerBasis`.

The **hard direction** (all S-polynomial remainders vanish → Gröbner basis) is the content
of Buchberger's theorem.  The proof uses `sPolynomial_decomposition` (Mathlib) together
with a degree induction.  We defer this direction via `sorry`.

## References

* [Becker-Weispfenning1993] §5.5 Theorem 5.64
-/

import Groebner.Defs

open MvPolynomial

namespace MonomialOrder

variable {σ : Type*} {k : Type*} [Field k] (m : MonomialOrder σ)

/-! ### S-polynomial remainder criterion -/

/-- Auxiliary predicate: all S-polynomial remainders in the list vanish. -/
def AllSpolyRemaindersZero (G : List (MvPolynomial σ k)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, remainder m G (m.sPolynomial p q) = 0

/-! #### Easy direction -/

/-- **Easy direction of Buchberger's criterion**: if `G` is a Gröbner basis for the ideal
`I = Ideal.span G`, then every S-polynomial reduces to zero modulo `G`.

Proof: `sPolynomial p q` is a linear combination of `p` and `q`, hence lies in `I`.
Since `G` is a Gröbner basis, `remainder_eq_zero_of_isGroebnerBasis` gives the result. -/
theorem allSpolyRemaindersZero_of_isGroebnerBasis
    {G : List (MvPolynomial σ k)}
    (hG : IsGroebnerBasis m {g | g ∈ G} (Ideal.span { g | g ∈ G })) :
    AllSpolyRemaindersZero m G := by
  intro p hp q hq
  apply remainder_eq_zero_of_isGroebnerBasis m hG
  -- Prove: m.sPolynomial p q ∈ Ideal.span { g | g ∈ G }
  -- Unfold: m.sPolynomial p q =
  --   monomial (m.degree q - m.degree p) (m.leadingCoeff q) * p
  --   - monomial (m.degree p - m.degree q) (m.leadingCoeff p) * q
  simp only [sPolynomial]
  apply Ideal.sub_mem
  · apply Ideal.mul_mem_left
    exact Ideal.subset_span hp
  · apply Ideal.mul_mem_left
    exact Ideal.subset_span hq

/-! #### Hard direction -/

/-- **Hard direction of Buchberger's criterion**: if all S-polynomial remainders of pairs
in `G` vanish modulo `G`, then `G` is a Gröbner basis for `Ideal.span G`.

**Proof strategy** (deferred):
Using `MonomialOrder.sPolynomial_decomposition` (Mathlib), one shows by induction on
`m.degree f` that every `f ∈ Ideal.span G` reduces to `0` modulo `G`.
Write `f = ∑ cᵢ * gᵢ` with `gᵢ ∈ G`.  If the leading monomials don't all cancel, the
leading monomial of `f` is divisible by some `m.degree gᵢ` — done.  If they do cancel,
`sPolynomial_decomposition` rewrites the cancelling top-degree part as a combination of
S-polynomials; each reduces to `0` by hypothesis and has strictly smaller degree, so the
induction hypothesis applies. -/
theorem isGroebnerBasis_of_allSpolyRemaindersZero
    {G : List (MvPolynomial σ k)}
    (hS : AllSpolyRemaindersZero m G) :
    IsGroebnerBasis m {g | g ∈ G} (Ideal.span { g | g ∈ G }) := by
  constructor
  · intro g hg
    exact Ideal.subset_span hg
  · sorry
    -- Deferred: show Ideal.span (m.leadingTerm '' ↑(Ideal.span {g | g ∈ G}))
    --         = Ideal.span (m.leadingTerm '' {g | g ∈ G})
    -- using sPolynomial_decomposition and degree induction.

/-- **Buchberger's Criterion** (biconditional): `G` is a Gröbner basis for `Ideal.span G`
if and only if every S-polynomial `S(p, q)` for `p, q ∈ G` reduces to `0` modulo `G`. -/
theorem buchberger_criterion {G : List (MvPolynomial σ k)} :
    IsGroebnerBasis m {g | g ∈ G} (Ideal.span { g | g ∈ G }) ↔
    AllSpolyRemaindersZero m G :=
  ⟨allSpolyRemaindersZero_of_isGroebnerBasis m,
   isGroebnerBasis_of_allSpolyRemaindersZero m⟩

end MonomialOrder
