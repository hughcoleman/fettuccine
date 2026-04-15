import Fettuccine.CMonomialOrder
import Fettuccine.CMvPolynomial

/-!
# Multivariate Polynomial Division

This file defines the division algorithm for `CMvPolynomial σ R` with respect to a monomial order.
-/

namespace CMonomial

variable {σ : Type*} [DecidableEq σ]

-- Predicate for monomial divisibility: `m₁` divides `m₂`.
def divides? (m₁ m₂ : CMonomial σ) : Prop :=
  ∀ i ∈ m₁.support, m₁ i ≤ m₂ i

instance (m₁ m₂ : CMonomial σ) : Decidable (divides? m₁ m₂) := by
  classical
  refine decidable_of_iff (∀ i : {i // i ∈ m₁.support}, m₁ i ≤ m₂ i) ?_
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h i
    exact h i i.property

/-- Divide monomials when possible, returning the quotient. -/
def divide (m₁ m₂ : CMonomial σ) : Option (CMonomial σ) :=
  if _ : divides? m₂ m₁ then
    some (m₁ - m₂)
  else
    none

lemma divides?_iff (m₁ m₂ : CMonomial σ) : divides? m₁ m₂ ↔ ∀ i, m₁ i ≤ m₂ i := by
  constructor
  · intro h i
    by_cases hi : i ∈ m₁.support
    · exact h i hi
    · simp [DFinsupp.notMem_support_iff.mp hi]
  · intro h i hi
    exact h i

lemma divides?_lcm_left (m₁ m₂ : CMonomial σ) : divides? m₁ (lcm m₁ m₂) := by
  intro i hi; simp [lcm, DFinsupp.zipWith_apply]

lemma divides?_lcm_right (m₁ m₂ : CMonomial σ) : divides? m₂ (lcm m₁ m₂) := by
  intro i hi; simp [lcm, DFinsupp.zipWith_apply]

lemma divide_eq_some_of_divides? {m₁ m₂ : CMonomial σ} (h : divides? m₂ m₁) :
    m₁.divide m₂ = some (m₁ - m₂) := by
  simp [divide, h]

end CMonomial

open CMonomialOrder
open scoped CMonomialOrder

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [DecidableEq R] [Field R]

namespace CMvPolynomial

variable (ord : CMonomialOrder σ)

/-- If `R` is a domain, then a polynomial ring over `R` is also a domain. -/
instance isDomain [IsDomain R] : IsDomain (CMvPolynomial σ R) := by
  sorry

/-- The statement that a given pair of polynomials are the quotient and remainder of a particular
    polynomial division. -/
def IsMvQuotientRemainder (f g q r : CMvPolynomial σ R) : Prop :=
  f = g * q + r ∧ (∀ m ∈ r.support, ¬ CMonomial.divides? in[ord](g) m)

/-- The support of a sum is contained in the union of the supports of its summands. -/
-- LATER: MOVE TO `CMvPolynomial.lean`.
lemma support_add_subset (f g : CMvPolynomial σ R) : (f + g).support ⊆ f.support ∪ g.support := by
  exact DFinsupp.support_add

/-- The support of a product is contained in the product of the supports of its factors. -/
-- LATER: MOVE TO `CMvPolynomial.lean`.
lemma support_mul_subset (f g : CMvPolynomial σ R) :
    (f * g).support ⊆ Finset.image₂ (· + ·) f.support g.support := by
  sorry

/-- The leading monomial of a sum is an element of the supports of the summands. -/
-- LATER: MOVE TO `CMonomialOrder.lean`.
lemma leadingMonomial_add_mem (f g : CMvPolynomial σ R) (h : f + g ≠ 0) :
    in[ord](f + g) ∈ f.support ∪ g.support := by
  exact (support_add_subset f g)
    (leadingMonomial_mem_support (ord := ord) (f + g) h)

/-- The leading monomial of a sum is bounded by the leading monomials of its summands. -/
-- LATER: MOVE TO `CMonomialOrder.lean`.
lemma leadingMonomial_add_le (f g : CMvPolynomial σ R) :
    ord.toSyn in[ord](f + g) ≤ max (ord.toSyn in[ord](f)) (ord.toSyn in[ord](g)) := by
  by_cases h : f + g = 0
  · simpa [h] using (ord.zero_le' (max _ _))
  · have hmem : in[ord](f + g) ∈ f.support ∪ g.support :=
      leadingMonomial_add_mem (ord := ord) f g h
    rcases Finset.mem_union.mp hmem with hf | hg
    · exact le_trans
        (le_leadingMonomial (ord := ord) f in[ord](f + g) hf)
        (le_max_left _ _)
    · exact le_trans
        (le_leadingMonomial (ord := ord) g in[ord](f + g) hg)
        (le_max_right _ _)

/-- The leading monomial of a product is the product of the leading monomials. -/
lemma leadingMonomial_mul (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
    in[ord](f * g) = in[ord](f) + in[ord](g) := by
  sorry

local instance : LinearOrder ord.syn := ord.lo

local instance : WellFoundedRelation ord.syn where
  rel := (· < ·)
  wf  := ord.wf.wf

/-- The division algorithm for multivariate polynomials. -/
def mvDivide (f g : CMvPolynomial σ R) (hg : g ≠ 0) : CMvPolynomial σ R × CMvPolynomial σ R :=
  if hf : f = 0 then
    (0, 0)
  else
    match hm : CMonomial.divide in[ord](f) in[ord](g) with
    | some m =>
      -- The leading term is divisible, so we can eliminate it.
      let c      := CMvPolynomial.ofMonomial m (leadingCoefficient ord f / leadingCoefficient ord g)
      let ⟨q, r⟩ := mvDivide (f - c * g) g hg
      (c + q, r)
    | none =>
      -- The leading terms aren't divisible, so move on to the tail of f.
      let lt_f   := leadingTerm ord f
      let ⟨q, r⟩ := mvDivide (f - lt_f) g hg
      (q, r + lt_f)
termination_by (f.support.card, ord.toSyn in[ord](f))
decreasing_by
  · sorry
  · sorry

/-- The quotient and remainder of multivariate polynomial division is uniquely determined. -/
theorem mvDivide.unique {f g q₁ q₂ r₁ r₂ : CMvPolynomial σ R} (hg : g ≠ 0)
    (h₁ : IsMvQuotientRemainder ord f g q₁ r₁) (h₂ : IsMvQuotientRemainder ord f g q₂ r₂) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  -- Unfold `IsMvQuotientRemainder` to obtain that `g * (q₁ - q₂) = r₂ - r₁`.
  unfold IsMvQuotientRemainder at h₁ h₂
  have h : g * (q₁ - q₂) = r₂ - r₁ := by
    calc
      g * (q₁ - q₂) = (g * q₁ + r₁) - (g * q₂ + r₁) := by ring
      _             = (g * q₂ + r₂) - (g * q₂ + r₁) := by aesop
      _             = r₂ - r₁                       := by ring
  -- If `q₁ = q₂`, then the conclusion follows, so suppose towards a contradiction that `q₁ ≠ q₂`.
  suffices hq : q₁ = q₂ by aesop
  by_contra hq
  -- Then, `in(r₂ - r₁)` can be given in terms of the initial monomials of `g` and `q₁ - q₂`.
  have hq0 : q₁ - q₂ ≠ 0 := sub_ne_zero.mpr hq
  have hin : in[ord](r₂ - r₁) = in[ord](g) + in[ord](q₁ - q₂) := by
    calc
      in[ord](r₂ - r₁) = in[ord](g * (q₁ - q₂))         := by aesop
      _                = in[ord](g) + in[ord](q₁ - q₂)  := by
                            apply leadingMonomial_mul <;> assumption
  -- Since we're working in an integral domain, it follows that `r₂ - r₁ ≠ 0`, and therefore
  -- `in(r₂ - r₁)` lies in the support of either `r₁` or `r₂`.
  have hr0 : r₂ - r₁ ≠ 0 := by aesop
  have hmem : in[ord](r₂ - r₁) ∈ r₁.support ∪ r₂.support := by
    have h₁ : in[ord](r₂ + (-r₁)) ∈ r₂.support ∪ (-r₁).support := by
      exact leadingMonomial_add_mem (ord := ord) r₂ (-r₁)
        (by simpa [sub_eq_add_neg] using hr0)
    have h₂ : in[ord](r₂ - r₁) ∈ r₂.support ∪ (-r₁).support := by
      simpa [sub_eq_add_neg] using h₁
    have h₃ : r₂.support ∪ (-r₁).support = r₁.support ∪ r₂.support := by
      -- For some reason, neither `rw` nor `simp` match this pattern without making it an explicit
      -- hypothesis...
      have h' : DFinsupp.support (-r₁) = DFinsupp.support r₁ :=
        DFinsupp.support_neg (f := r₁)
      simp [h', Finset.union_comm]
    exact h₃ ▸ h₂
  -- In either case, it follows that `g` divides either `r₁` or `r₂`, contradicting the property of
  -- the remainder.
  have hdiv : CMonomial.divides? in[ord](g) in[ord](r₂ - r₁) := by
    rw [hin, CMonomial.divides?_iff]
    intro i; exact Nat.le_add_right (in[ord](g) i) (in[ord](q₁ - q₂) i)
  rcases Finset.mem_union.mp hmem with hr₁ | hr₂
  · exact (h₁.2 _ hr₁) hdiv
  · exact (h₂.2 _ hr₂) hdiv

/-- The results of `mvDivide` satisfy the division relation and remainder constraints. -/
theorem mvDivide.correct (f g : CMvPolynomial σ R) (hg : g ≠ 0) :
    let (q, r) := mvDivide ord f g hg
    IsMvQuotientRemainder ord f g q r := by
  sorry

end CMvPolynomial
