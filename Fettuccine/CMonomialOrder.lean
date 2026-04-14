import Fettuccine.CMvPolynomial
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Computable Monomial Orders

This file defines `CMonomialOrder`, a structure representing monomial orders on `CMonomial σ`, and
provides the lexicographic (lex) monomial order. For the most part, the structure of this file
largely mirrors Mathlib/Data/Finsupp/MonomialOrder.lean.

## Definitions

* `CMonomialOrder σ` : a well-founded, translation-invariant total order on `CMonomial σ`.
* `CMonomialOrder.lex` : the lexicographic order on monomials.
* `CMvPolynomial.leadingMonomial` : the leading monomial of a multivariate polynomial with respect
  to a monomial order.

## Notation

* `m₁ ≺[ord] m₂` : strict inequality under the monomial order `ord`.
* `m₁ ≼[ord] m₂` : inequality under the monomial order `ord`.
-/

/-- A **monomial order** on `σ` is a well-founded, translation-invariant (decidable) total order on
    `CMonomial σ`. -/
structure CMonomialOrder (σ : Type*) [DecidableEq σ] where
  /-- The synonym type from which the order is lifted. -/
  syn : Type*
  /-- `syn` is an additive commutative monoid. -/
  acm : AddCommMonoid syn
  /-- `syn` is linearly ordered. -/
  lo : LinearOrder syn
  /-- `syn` is an additive monoid and cancellative under the linear order. -/
  iocam : IsOrderedCancelAddMonoid syn
  /-- The (additive) equivalence of `CMonomial σ` in `syn`. -/
  toSyn : (CMonomial σ) ≃+ syn
  /-- `toSyn` is monotone on the pointwise order. -/
  toSyn_monotone : Monotone toSyn.toFun
  /-- `syn` is well-ordered. -/
  wf : WellFoundedLT syn

attribute [instance] CMonomialOrder.acm CMonomialOrder.lo CMonomialOrder.iocam CMonomialOrder.wf

namespace CMonomialOrder

-- Notation for using the order on the synonym type.
section Notation

/-- Notation for the strict order relation for monomial orders. -/
scoped notation:50 m₁ " ≺[" ord:25 "] " m₂:50 =>
  (CMonomialOrder.toSyn ord m₁ < CMonomialOrder.toSyn ord m₂)

/-- Notation for the order relation for monomial orders. -/
scoped notation:50 m₁ " ≼[" ord:25 "] " m₂:50 =>
  (CMonomialOrder.toSyn ord m₁ ≤ CMonomialOrder.toSyn ord m₂)

end Notation

variable {σ : Type*} [DecidableEq σ] (ord : CMonomialOrder σ)

-- Zero is a minimal element of any monomial order.
lemma zero_le' (m : ord.syn) : 0 ≤ m := by
  by_contra h; push_neg at h
  -- If 0 > m, then by translation-invariance we can construct the infinitely-descending sequence
  -- 0 > m > m² > m³ > ⋯.
  have h' (n : ℕ) : (n + 1) • m < n • m := by
    induction n <;> simpa [one_nsmul, succ_nsmul]
  -- This contradicts the well-foundedness of the order.
  exact WellFounded.not_rel_apply_succ (fun n => (n • m))
    |>.elim (fun n hn => hn (h' n))

lemma zero_le (m : CMonomial σ) : 0 ≼[ord] m := by
  simp [ord.toSyn.map_zero, zero_le']

-- The order is monotone.
lemma le_add_right' (m₁ m₂ : ord.syn) : m₁ ≤ m₁ + m₂ := by
  calc m₁ = m₁ + 0   := (add_zero _).symm
       _  ≤ m₁ + m₂  := add_le_add_right (ord.zero_le' m₂) m₁

lemma le_add_right (m₁ m₂ : CMonomial σ) : m₁ ≼[ord] m₁ + m₂ := by
  rw [ord.toSyn.map_add]
  exact ord.le_add_right' (ord.toSyn m₁) (ord.toSyn m₂)

-- If a sum of monomials attains a sum of upper bounds, then the summands each attain their upper
-- bound.
lemma eq_of_add_eq_of_le' {m₁ m₂ m₁' m₂' : ord.syn}
    (h₁ : m₁' ≤ m₁) (h₂ : m₂' ≤ m₂) (h : m₁' + m₂' = m₁ + m₂) :
    m₁' = m₁ ∧ m₂' = m₂ := by
  have hle₁ : m₁' + m₂' ≤ m₁ + m₂' := add_le_add_left  h₁ m₂'
  have hle₂ : m₁  + m₂' ≤ m₁ + m₂  := add_le_add_right h₂ m₁
  -- These inequalities are, in fact, equalities. By cancellation, the result follows.
  have heq₁ : m₁' + m₂' = m₁ + m₂' := le_antisymm hle₁ (h ▸ hle₂)
  have heq₂ : m₁  + m₂' = m₁ + m₂  := le_antisymm hle₂ (h ▸ hle₁)
  exact ⟨add_right_cancel heq₁, add_left_cancel heq₂⟩

lemma eq_of_add_eq_of_le {m₁ m₂ m₁' m₂' : CMonomial σ}
    (h₁ : m₁' ≼[ord] m₁) (h₂ : m₂' ≼[ord] m₂) (h : m₁' + m₂' = m₁ + m₂) :
    m₁' = m₁ ∧ m₂' = m₂ := by
  sorry
  -- exact ord.eq_of_add_eq_of_le' (ord.toSyn_monotone h₁) (ord.toSyn_monotone h₂) h

/-- A monomial order is **graded** if it respects homogeneity. -/
def IsGraded : Prop :=
  ∀ m₁ m₂ : CMonomial σ, m₁.degree < m₂.degree → m₁ ≺[ord] m₂

end CMonomialOrder

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]

/-- The lexicographic order on monomials. -/
def lex [WellFoundedGT σ] : CMonomialOrder σ where
  syn   := Lex (Π₀ _ : σ, ℕ)
  acm   := by
    rw [Lex] -- unwrap the synonym type
    infer_instance
  lo    := DFinsupp.Lex.linearOrder
  iocam := DFinsupp.Lex.isOrderedCancelAddMonoid
  toSyn :=
    { toEquiv :=
        { toFun     := id
          invFun    := id
          left_inv  := fun m => DFinsupp.ext (congrFun rfl)
          right_inv := fun m => rfl }
      map_add' := fun m₁ m₂ => rfl }
  toSyn_monotone := fun a b h => by
    exact DFinsupp.toLex_monotone (α := fun (_ : σ) => ℕ) h
  wf    := DFinsupp.Lex.wellFoundedLT

end CMonomialOrder

section LeadingMonomial

variable {σ : Type*} [DecidableEq σ] (ord : CMonomialOrder σ)
variable {R : Type*} [DecidableEq R] [CommSemiring R]

namespace CMvPolynomial

/-- The **leading monomial** of a polynomial `f` with respect to a monomial order `ord`. By
    convention, this is typically zero for the zero polynomial but we are good computer scientists
    so we will use the `Option` type. -/
def leadingMonomial (f : CMvPolynomial σ R) : Option (CMonomial σ) :=
  let supp := f.support
  if h : supp.Nonempty then
    -- FIXME: This is ugly...
    some (ord.toSyn.symm ((supp.image ord.toSyn).max' (h.image _)))
  else
    none

/-- The leading monomial of the zero polynomial is none. -/
lemma leadingMonomial_zero : (0 : CMvPolynomial σ R).leadingMonomial ord = none := by
  simp [leadingMonomial]

-- /-- The leading monomial of a non-zero polynomial is an element of its support. -/
-- lemma leadingMonomial_eq_some_of_nonempty (f : CMvPolynomial σ R) (hf : f.support.Nonempty) :
--     leadingMonomial f = some (f.support.max' hf) := by
--   simp [leadingMonomial, hf]

-- /-- The leading monomial belongs to the support. -/
-- lemma leadingMonomial_mem_support (f : CMvPolynomial σ R) (hf : f.support.Nonempty) :
--     f.support.max' hf ∈ f.support := by
--   exact f.support.max'_mem hf

-- /-- The leading monomial is indeed an upper bound for the support. -/
-- lemma le_leadingMonomial (f : CMvPolynomial σ R) {m : CMonomial σ} (hm : m ∈ f.support) :
--     m ≤ f.support.max' ⟨m, hm⟩ := by
--   exact Finset.le_max' _ _ hm

-- /-- The leading monomial of a single term c * m is just m (when c ≠ 0) -/
-- lemma leadingMonomial_monomial (m : CMonomial σ) (c : R) (hc : c ≠ 0) :
--     leadingMonomial (CMvPolynomial.ofMonomial m c) = some m := by
--   rw [leadingMonomial_eq_some_of_nonempty _ (by simp [support_ofMonomial m c hc])]
--   simp [support_ofMonomial m c hc, Finset.max'_singleton]

-- /-- The leading monomial of a product is the product of leading monomials. -/
-- lemma leadingMonomial_mul' (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
--     leadingMonomial (f * g) = (leadingMonomial f).map₂ (· + ·) (leadingMonomial g) := by
--   sorry

-- lemma leadingMonomial_mul (f g : CMvPolynomial σ R) :
--     leadingMonomial (f * g) = (leadingMonomial f).map₂ (· + ·) (leadingMonomial g) := by
--   by_cases hf : f = 0
--   · simp [hf, leadingMonomial_zero]
--   by_cases hg : g = 0
--   · simp [hg, leadingMonomial_zero]
--   exact leadingMonomial_mul' f g hf hg

-- /-- The leading monomial of a sum is bounded by the larger of the leading
--     monomials of the summands. -/
-- lemma leadingMonomial_add_le' (f g : CMvPolynomial σ R)
--     (hf : f.support.Nonempty) (hg : g.support.Nonempty) (hfg : (f + g).support.Nonempty) :
--     (f + g).support.max' hfg ≤ max (f.support.max' hf) (g.support.max' hg) :=
--   sorry

end CMvPolynomial

end LeadingMonomial
