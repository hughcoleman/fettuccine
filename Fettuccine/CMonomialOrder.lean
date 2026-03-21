import Fettuccine.CMvPolynomial
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Computable monomial orders

This file defines `CMonomialOrder`, a typeclass for monomial orders on
`CMonomial σ`, and provides an instance for the lexicographic order.

## Definitions

* `CMonomialOrder σ` : a well-founded, translation-invariant total order on
  `CMonomial σ`.
* `CMonomialOrder.lex` : the lexicographic order on monomials.

## Notation

* `m₁ ≺[ord] m₂` : strict inequality under the monomial order `ord`.
* `m₁ ≼[ord] m₂` : inequality under the monomial order `ord`.
-/

/-- A **monomial order** on `σ` is a well-founded, translation-invariant total
    order on `CMonomial σ`. -/
class CMonomialOrder (σ : Type*) [DecidableEq σ] extends
  LinearOrder (CMonomial σ),
  IsOrderedCancelAddMonoid (CMonomial σ),
  WellFoundedLT (CMonomial σ)

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ] (ord : CMonomialOrder σ)

def lt' (m₁ m₂ : CMonomial σ) : Prop :=
  @LT.lt _ ord.toLT m₁ m₂

def le' (m₁ m₂ : CMonomial σ) : Prop :=
  @LE.le _ ord.toLE m₁ m₂

section Notation

/-- Notation for the strict order relation for monomial orders. -/
scoped notation:50 lhs " ≺[" ord "] " rhs => CMonomialOrder.lt' ord lhs rhs

/-- Notation for the order relation for monomial orders. -/
scoped notation:50 lhs " ≼[" ord "] " rhs => CMonomialOrder.le' ord lhs rhs

end Notation

lemma zero_le (m : CMonomial σ) : 0 ≼[ord] m := by
  simp only [le']
  -- If 0 > m, then by translation invariance it follows that we have a
  -- descending sequence 0 > m > m² > m³ > ...
  by_contra h; push_neg at h
  have hdesc : ∀ n : ℕ, (n + 1) • m < n • m := by
    intro n
    induction n with
    | zero      => simp_all only [zero_add, zero_nsmul, one_nsmul]
    | succ n ih => simp_all only [succ_nsmul, add_lt_iff_neg_left]
  -- This sequence contradicts the well-foundedness of the order.
  haveI : IsWellFounded (CMonomial σ) (· < ·) := inferInstance
  exact WellFounded.not_rel_apply_succ (fun n => n • m) |>.elim (fun n hn => hn (hdesc n))

/-- If a sum of monomials is attains a sum of upper bounds, then the summands
    each attain their upper bound. -/
lemma eq_of_add_eq_of_le {m₁ m₂ m₁' m₂' : CMonomial σ}
    (h₁ : m₁' ≼[ord] m₁) (h₂ : m₂' ≼[ord] m₂) (h : m₁' + m₂' = m₁ + m₂) :
    m₁' = m₁ ∧ m₂' = m₂ := by
  have hle₁ : m₁' + m₂' ≤ m₁ + m₂' := add_le_add_left  h₁ m₂'
  have hle₂ : m₁  + m₂' ≤ m₁ + m₂  := add_le_add_right h₂ m₁
  -- These inequalities are, in fact, equalities. By cancellation, the result
  -- follows.
  have heq₁ : m₁' + m₂' = m₁ + m₂' := le_antisymm hle₁ (h ▸ hle₂)
  have heq₂ : m₁  + m₂' = m₁ + m₂  := le_antisymm hle₂ (h ▸ hle₁)
  exact ⟨add_right_cancel heq₁, add_left_cancel heq₂⟩

end CMonomialOrder

namespace CMvPolynomial

section LeadingMonomial

variable {σ : Type*} [DecidableEq σ] (ord : CMonomialOrder σ)
variable {R : Type*} [DecidableEq R] [CommSemiring R]

/-- The **leading monomial** of a polynomial `f` with respect to a monomial
    order `ord`. By convention, this is typically zero for the zero polynomial
    but we are good computer scientists so we will use the `Option` type. -/
def leadingMonomial (f : CMvPolynomial σ R) : Option (CMonomial σ) :=
  let supp := f.support
  if h : supp.Nonempty then
    some (supp.max' h)
  else
    none

/-- The leading monomial of the zero polynomial is none. -/
lemma leadingMonomial_zero : leadingMonomial ord (0 : CMvPolynomial σ R) = none := by
  simp [leadingMonomial]; rfl

/-- The leading monomial of a non-zero polynomial is an element of its support. -/
lemma leadingMonomial_eq_some_of_nonempty (f : CMvPolynomial σ R) (hf : f.support.Nonempty) :
    leadingMonomial ord f = some (f.support.max' hf) := by
  simp [leadingMonomial, hf]

/-- The leading monomial belongs to the support. -/
lemma leadingMonomial_mem_support (f : CMvPolynomial σ R) (hf : f.support.Nonempty) :
    f.support.max' hf ∈ f.support := by
  exact Finset.max'_mem f.support hf

/- The leading monomial is none if and only if the polynomial is zero. -/
lemma leadingMonomial_eq_none_iff (f : CMvPolynomial σ R) :
    leadingMonomial ord f = none ↔ f = 0 := by
  sorry

/-- The leading monomial is indeed an upper bound for the support. -/
lemma le_leadingMonomial (f : CMvPolynomial σ R) {m : CMonomial σ} (hm : m ∈ f.support) :
    m ≤ f.support.max' ⟨m, hm⟩ := by
  exact Finset.le_max' _ _ hm

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

end LeadingMonomial

/-! ## Monomial Orders -/

/-! ### Lex -/

section Lex

open CMonomialOrder

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]

/-- Lift the lexicographic order to a linear order on `CMonomial σ`. -/
instance : LinearOrder (CMonomial σ) :=
  LinearOrder.lift' (fun m => toLex m.toFun)
    (fun m₁ m₂ h => by cases m₁; cases m₂; simp_all)

/-- Lift the well-foundedness of the lexicographic order. -/
instance [WellFoundedGT σ] : WellFoundedLT (CMonomial σ) :=
  ⟨InvImage.wf (fun (m : CMonomial σ) => toLex m.toFun) DFinsupp.Lex.wellFoundedLT.wf⟩

@[simp] lemma lex_le_iff (m₁ m₂ : CMonomial σ) :
    m₁ ≤ m₂ ↔ toLex m₁.toFun ≤ toLex m₂.toFun := Iff.rfl

@[simp] lemma toFun_add (m₁ m₂ : CMonomial σ) :
    (m₁ + m₂).toFun = m₁.toFun + m₂.toFun := by
  rfl

/-- The lexicographic order on `CMonomial σ`. -/
instance lex [WellFoundedGT σ] : CMonomialOrder σ where
  add_le_add_left m₁ m₂ h m := by
    rw [lex_le_iff, toFun_add] at *
    exact add_le_add_left h _
  le_of_add_le_add_left m m₁ m₂ h := by
    change toLex m₁.toFun ≤ toLex m₂.toFun
    exact le_of_add_le_add_left h

end Lex

/-! ### Grlex -/

section Grlex

-- /-- The graded lexicographic order on `CMonomial σ`. -/

end Grlex

/-! ### Grevlex -/

section Grevlex

-- /-- The graded reverse lexicographic order on `CMonomial σ`. -/

end Grevlex

end CMvPolynomial
