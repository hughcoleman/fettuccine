import Fettuccine.CMvPolynomial
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Computable Monomial Orders

This file defines `CMonomialOrder`, a typeclass for monomial orders on `CMonomial σ`, and provides
instances for the lexicographic (lex), graded lexicographic (grlex), and graded reverse
lexicographic (grevlex) orders.

## Definitions

* `CMonomialOrder σ` : a well-founded, translation-invariant total order on `CMonomial σ`.
* `CMonomialOrder.Lex.lex` : the lexicographic order on monomials.
* `CMonomialOrder.Grlex.grlex` : the graded lexicographic order on monomials.
* `CMonomialOrder.Grevlex.grevlex` : the graded reverse lexicographic order on monomials.
* `CMvPolynomial.leadingMonomial` : the leading monomial of a multivariate polynomial with respect
  to a monomial order.

## Notation

* `m₁ ≺[ord] m₂` : strict inequality under the monomial order `ord`.
* `m₁ ≼[ord] m₂` : inequality under the monomial order `ord`.
-/

/-- A **monomial order** on `σ` is a well-founded, translation-invariant, decidable total order on
    `CMonomial σ`. -/
-- This pretty blatantly copies the structure of Mathlib/Data/Finsupp/MonomialOrder.lean, but
-- perhaps this will turn out to be a desirable property.
structure CMonomialOrder (σ : Type*) [DecidableEq σ] where
  /-- The synonym type from which the order is lifted. -/
  syn : Type*
  /-- `syn` is an additive commutative monoid. -/
  acm : AddCommMonoid syn
  /-- `syn` is linearly ordered. -/
  lo : LinearOrder syn
  /-- `syn` is a linearly ordered cancellative additive commutative monoid. -/
  iocam : IsOrderedCancelAddMonoid syn
  /-- `syn` is a well-ordering. -/
  wf : WellFoundedLT syn
  /-- The order on `syn` is decidable. -/
  dec : DecidableRel (α := syn) (· ≤ ·)
  /-- The embedding of `CMonomial σ` in `syn`. -/
  toSyn : (CMonomial σ) →+ syn
  /-- The embedding is injective. -/
  toSyn_injective : Function.Injective toSyn.toFun

attribute [instance]
  CMonomialOrder.acm CMonomialOrder.lo CMonomialOrder.iocam CMonomialOrder.wf CMonomialOrder.dec

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ] (ord : CMonomialOrder σ)

-- Zero is a minimal element of any monomial order.
private lemma zero_le' (m : ord.syn) : 0 ≤ m := by
  by_contra h; push_neg at h
  -- Assuming that 0 > m, then by translation-invariance we can construct the infinitely
  -- descending sequence 0 > m > m² > m³ > ⋯.
  have h' (n : ℕ) : (n + 1) • m < n • m := by
    induction n <;> simpa [one_nsmul, succ_nsmul]
  -- This contradicts the well-foundedness of the order.
  exact WellFounded.not_rel_apply_succ (fun n => (n • m))
    |>.elim (fun n hn => hn (h' n))

-- The order is monotone.
private lemma le_add_right' (m₁ m₂ : ord.syn) : m₁ ≤ m₁ + m₂ := by
  calc
    m₁ = m₁ + 0   := (add_zero _).symm
    _  ≤ m₁ + m₂  := add_le_add_right (ord.zero_le' m₂) m₁

-- If a sum of monomials attains a sum of upper bounds, then the summands each attain their upper
-- bound.
private lemma eq_of_add_eq_of_le' {m₁ m₂ m₁' m₂' : ord.syn}
    (h₁ : m₁' ≤ m₁) (h₂ : m₂' ≤ m₂) (h : m₁' + m₂' = m₁ + m₂) :
    m₁' = m₁ ∧ m₂' = m₂ := by
  have hle₁ : m₁' + m₂' ≤ m₁ + m₂' := add_le_add_left  h₁ m₂'
  have hle₂ : m₁  + m₂' ≤ m₁ + m₂  := add_le_add_right h₂ m₁
  -- These inequalities are, in fact, equalities. By cancellation, the result follows.
  have heq₁ : m₁' + m₂' = m₁ + m₂' := le_antisymm hle₁ (h ▸ hle₂)
  have heq₂ : m₁  + m₂' = m₁ + m₂  := le_antisymm hle₂ (h ▸ hle₁)
  exact ⟨add_right_cancel heq₁, add_left_cancel heq₂⟩

/-- Notation for the strict order relation for monomial orders. -/
scoped notation:50 m₁ " ≺[" ord:25 "] " m₂:50 =>
  (CMonomialOrder.toSyn ord m₁ < CMonomialOrder.toSyn ord m₂)

/-- Notation for the order relation for monomial orders. -/
scoped notation:50 m₁ " ≼[" ord:25 "] " m₂:50 =>
  (CMonomialOrder.toSyn ord m₁ ≤ CMonomialOrder.toSyn ord m₂)

-- Let's restate the lemmas for `sym` in terms of monomials.

/-- Zero is a minimal element of any monomial order. -/
lemma zero_le (m : CMonomial σ) : 0 ≼[ord] m := by
  simp [ord.toSyn.map_zero, zero_le']

/-- The order is monotone. -/
lemma le_add_right (m₁ m₂ : CMonomial σ) : m₁ ≼[ord] m₁ + m₂ := by
  rw [ord.toSyn.map_add]
  exact ord.le_add_right' (ord.toSyn m₁) (ord.toSyn m₂)

variable [LinearOrder σ]

section Lex

/-- The lexicographic order on monomials. -/
def lex [WellFoundedGT σ] : (CMonomialOrder σ) where
  -- We use the lexicographic order on `Π₀ _ : σ, ℕ`.
  syn := Lex (Π₀ _ : σ, ℕ)
  -- Most instances can be synthesized by inference.
  acm   := instAddCommMonoidLex
  lo    := DFinsupp.Lex.linearOrder
  iocam := DFinsupp.Lex.isOrderedCancelAddMonoid
  wf    := DFinsupp.Lex.wellFoundedLT
  dec   := DFinsupp.Lex.decidableLE
  -- The equivalence is given by `toLex`.
  toSyn := {
    toFun m         := toLex m.toFun
    map_zero'       := toLex_eq_zero.mpr rfl
    map_add' m₁ m₂  := (Equiv.apply_eq_iff_eq_symm_apply toLex).mpr rfl
  }
  toSyn_injective   := by
    intros m₁ m₂ h; cases m₁; cases m₂; simp_all

end Lex

def IsGraded (ord : CMonomialOrder σ) : Prop :=
  ∀ m₁ m₂ : CMonomial σ, m₁.degree < m₂.degree → m₁ ≺[ord] m₂

section Grlex

instance instGrlexIsOrderedCancelAddMonoid :
    IsOrderedCancelAddMonoid (Lex (ℕ × Lex (Π₀ _ : σ, ℕ))) where
  add_le_add_left := fun a b h c => by
    simp only [Prod.Lex.le_iff] at *
    rcases h with h | ⟨h, h'⟩
    · left; exact add_lt_add_left h _
    · right; exact ⟨by simp; omega, add_le_add_left h' _⟩
  le_of_add_le_add_left := fun a b c h => by
    simp only [Prod.Lex.le_iff] at *
    rcases h with h | ⟨h, h'⟩
    · left; exact lt_of_add_lt_add_left h
    · right; exact ⟨add_left_cancel h, le_of_add_le_add_left h'⟩

instance instGrlexWellFoundedLT [WellFoundedGT σ] : WellFoundedLT (Lex (ℕ × Lex (Π₀ _ : σ, ℕ))) :=
  ⟨InvImage.wf (fun (p : Lex (ℕ × Lex (Π₀ _ : σ, ℕ))) => (p.1, p.2))
    (WellFounded.prod_lex Nat.lt_wfRel.wf DFinsupp.Lex.wellFoundedLT.wf)⟩

/-- The graded lexicographic order on monomials. -/
def grlex [WellFoundedGT σ] : (CMonomialOrder σ) where
  -- We use the graded lexicographic order on `ℕ × Lex (Π₀ _ : σ, ℕ)`.
  syn := Lex (ℕ × Lex (Π₀ _ : σ, ℕ))
  -- Most instances can be synthesized by inference.
  acm   := instAddCommMonoidLex
  lo    := Prod.Lex.instLinearOrder _ _
  iocam := instGrlexIsOrderedCancelAddMonoid
  wf    := instGrlexWellFoundedLT
  dec   := Prod.Lex.instDecidableRelOfDecidableEq
  -- The additive equivalence given by `toLex`, augmented with the degree.
  toSyn := {
    toFun m         := (m.degree, toLex m.toFun),
    map_zero'       := ofLex_eq_zero.mp rfl,
    map_add' m₁ m₂  := by
      simp [CMonomial.degree_add, CMonomial.toFun_add]
      rfl
  }
  toSyn_injective := by
    intros m₁ m₂ h
    have h' : toLex m₁.toFun = toLex m₂.toFun :=
      congr_arg Prod.snd h
    cases m₁; cases m₂; simp_all

/-- The graded lexicographic order on monomials is graded. -/
lemma grlex.IsGraded [wf : WellFoundedGT σ] : IsGraded (@grlex _ _ _ wf) := by
  intros m₁ m₂ h
  change
    toLex (m₁.degree, toLex m₁.toFun) < toLex (m₂.degree, toLex m₂.toFun)
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

end Grlex

section Grevlex

instance instGrevlexIsOrderedCancelAddMonoid :
    IsOrderedCancelAddMonoid (Lex (ℕ × OrderDual (Lex (Π₀ _ : OrderDual σ, ℕ)))) where
  add_le_add_left := fun a b h c => by
    simp only [Prod.Lex.le_iff] at *
    rcases h with h | ⟨h, h'⟩
    · left; exact add_lt_add_left h _
    · right; exact ⟨by simp; omega, add_le_add_left h' _⟩
  le_of_add_le_add_left := fun a b c h => by
    simp only [Prod.Lex.le_iff] at *
    rcases h with h | ⟨h, h'⟩
    · left; exact lt_of_add_lt_add_left h
    · right; exact ⟨add_left_cancel h, le_of_add_le_add_left h'⟩

/-- The graded reverse lexicographic order on monomials. -/
def grevlex [WellFoundedGT σ] : (CMonomialOrder σ) where
  -- We use the graded reverse lexicographic order on `ℕ × OrderDual (Lex (Π₀ _ : OrderDual σ, ℕ))`.
  syn := Lex (ℕ × OrderDual (Lex (Π₀ _ : OrderDual σ, ℕ)))
  -- Most instances can be synthesized by inference.
  acm   := instAddCommMonoidLex
  lo    := Prod.Lex.instLinearOrder _ _
  iocam := instGrevlexIsOrderedCancelAddMonoid
  wf    := sorry
  dec   := Prod.Lex.instDecidableRelOfDecidableEq
  -- The additive equivalence given by `toLex`, augmented with the degree.
  toSyn := {
    toFun m         := (m.degree, toLex m.toFun),
    map_zero'       := ofLex_eq_zero.mp rfl,
    map_add' m₁ m₂  := by
      simp [CMonomial.degree_add, CMonomial.toFun_add]
      rfl
  }
  toSyn_injective := by
    intros m₁ m₂ h
    have h' : toLex m₁.toFun = toLex m₂.toFun :=
      congr_arg Prod.snd h
    cases m₁; cases m₂; simp_all

/-- The graded reverse lexicographic order on monomials is graded. -/
lemma grevlex.IsGraded [wf : WellFoundedGT σ] : IsGraded (@grevlex _ _ _ wf) := by
  sorry

end Grevlex

end CMonomialOrder

section LeadingMonomial

namespace CMvPolynomial

variable {σ : Type*} [DecidableEq σ] (ord : CMonomialOrder σ)
variable {R : Type*} [DecidableEq R] [CommSemiring R]

/-- The **leading monomial** of a polynomial `f` with respect to a monomial order `ord`. By
    convention, this is typically zero for the zero polynomial but we are good computer scientists
    so we will use the `Option` type. -/
def leadingMonomial (f : CMvPolynomial σ R) : Option (CMonomial σ) :=
  let supp := f.support
  if h : supp.Nonempty then
    some sorry -- some (supp.max' h)
  else
    none

-- /-- The leading monomial of the zero polynomial is none. -/
-- lemma leadingMonomial_zero : leadingMonomial ord (0 : CMvPolynomial σ R) = none := by
--   simp [leadingMonomial]; rfl

-- /-- The leading monomial of a non-zero polynomial is an element of its support. -/
-- lemma leadingMonomial_eq_some_of_nonempty (f : CMvPolynomial σ R) (hf : f.support.Nonempty) :
--     leadingMonomial ord f = some (f.support.max' hf) := by
--   simp [leadingMonomial, hf]

-- /-- The leading monomial belongs to the support. -/
-- lemma leadingMonomial_mem_support (f : CMvPolynomial σ R) (hf : f.support.Nonempty) :
--     f.support.max' hf ∈ f.support := by
--   exact Finset.max'_mem f.support hf

-- /- The leading monomial is none if and only if the polynomial is zero. -/
-- lemma leadingMonomial_eq_none_iff (f : CMvPolynomial σ R) :
--     leadingMonomial ord f = none ↔ f = 0 := by
--   sorry

-- /-- The leading monomial is indeed an upper bound for the support. -/
-- lemma le_leadingMonomial (f : CMvPolynomial σ R) {m : CMonomial σ} (hm : m ∈ f.support) :
--     m ≤ f.support.max' ⟨m, hm⟩ := by
--   exact Finset.le_max' _ _ hm

-- /-- The leading monomial of a single term c * m is just m (when c ≠ 0) -/
-- lemma leadingMonomial_monomial (ord : CMonomialOrder σ) (m : CMonomial σ) (c : R) (hc : c ≠ 0) :
--     leadingMonomial ord (CMvPolynomial.ofMonomial c m) = some m := by
--   sorry

-- /-- The leading monomial of a product is the product of leading monomials. -/
-- lemma leadingMonomial_mul (ord : CMonomialOrder σ) (f g : CMvPolynomial σ R)
--     (hf : f ≠ 0) (hg : g ≠ 0) :
--     leadingMonomial ord (f * g) = (leadingMonomial ord f).map₂ (· * ·) (leadingMonomial ord g) :=
--   sorry

-- /-- The leading monomial of a sum is bounded by the larger of the leading
--     monomials of the summands. -/
-- lemma leadingMonomial_add_le (ord : CMonomialOrder σ) (f g : CMvPolynomial σ R)
--     (hf : f.support.Nonempty) (hg : g.support.Nonempty) (h : (f + g).support.Nonempty) :
--     (f + g).support.max' h ≤ max (f.support.max' hf) (g.support.max' hg) :=
--   sorry

end CMvPolynomial

end LeadingMonomial
