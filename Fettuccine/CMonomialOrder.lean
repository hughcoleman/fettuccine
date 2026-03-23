import Fettuccine.CMvPolynomial
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Computable Monomial Orders

This file defines `CMonomialOrder`, a typeclass for monomial orders on `CMonomial σ`, and provides
instances for the lexicographic (lex), graded lexicographic (grlex), and graded reverse
lexicographic (grevlex) orders.

## Definitions

* `CMonomialOrder σ` : a well-founded, translation-invariant total order on `CMonomial σ`.
* `CMonomialOrder.lex` : the lexicographic order on monomials.
* `CMonomialOrder.grlex` : the graded lexicographic order on monomials.
* `CMonomialOrder.grevlex` : the graded reverse lexicographic order on monomials.
* `CMvPolynomial.leadingMonomial` : the leading monomial of a multivariate polynomial with respect
  to a monomial order.

## Notation

* `m₁ ≺ m₂` : strict inequality under the (inferred) monomial order.
* `m₁ ≼ m₂` : inequality under the (inferred) monomial order.
* `m₁ ≺[ord] m₂` : strict inequality under the monomial order `ord`.
* `m₁ ≼[ord] m₂` : inequality under the monomial order `ord`.
-/

/-- A **monomial order** on `σ` is a well-founded, translation-invariant, decidable total order on
    `CMonomial σ`. -/
-- This pretty blatantly copies the structure of Mathlib/Data/Finsupp/MonomialOrder.lean, but
-- perhaps this will turn out to be a desirable property of our definition.
class CMonomialOrder (σ : Type*) [DecidableEq σ] where
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

attribute [reducible, instance] CMonomialOrder.acm CMonomialOrder.lo CMonomialOrder.dec
attribute [instance] CMonomialOrder.iocam CMonomialOrder.wf

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ] [ord : CMonomialOrder σ]

-- We can lift the order on `syn` up to `CMonomial σ`.
instance toLinearOrder : LinearOrder (CMonomial σ) :=
  LinearOrder.lift' ord.toSyn ord.toSyn_injective

/-- Notation for the strict order relation for monomial orders. -/
scoped notation:50 m₁ " ≺ " m₂ =>
  CMonomialOrder.toSyn m₁ < CMonomialOrder.toSyn m₂
scoped notation:50 m₁ " ≺[" ord "] " m₂ =>
  @CMonomialOrder.toSyn _ _ ord m₁ < @CMonomialOrder.toSyn _ _ ord m₂

/-- Notation for the order relation for monomial orders. -/
scoped notation:50 m₁ " ≼ " m₂ =>
  CMonomialOrder.toSyn m₁ ≤ CMonomialOrder.toSyn m₂
scoped notation:50 m₁ " ≼[" ord "] " m₂ =>
  @CMonomialOrder.toSyn _ _ ord m₁ ≤ @CMonomialOrder.toSyn _ _ ord m₂

-- Zero is a minimal element of any monomial order.
lemma zero_le' (m : ord.syn) : 0 ≤ m := by
  by_contra h; push_neg at h
  -- Assuming that 0 > m, then by translation-invariance we can construct the infinitely
  -- descending sequence 0 > m > m² > m³ > ⋯.
  have h' (n : ℕ) : (n + 1) • m < n • m := by
    induction n <;> simpa [one_nsmul, succ_nsmul]
  -- This contradicts the well-foundedness of the order.
  exact WellFounded.not_rel_apply_succ (fun n => (n • m))
    |>.elim (fun n hn => hn (h' n))

lemma zero_le (m : CMonomial σ) : 0 ≼[ord] m := by
  simp [CMonomialOrder.toSyn.map_zero, zero_le']

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

section Instances

variable [DecidableEq σ] [LinearOrder σ] [WellFoundedLT σ]

instance instLexIsOrderedCancelAddMonoid {α β : Type*}
    [AddCancelCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [AddCancelCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β] :
    IsOrderedCancelAddMonoid (Lex (α × β)) where
  add_le_add_left := fun a b h c => by
    simp only [Prod.Lex.le_iff] at *
    rcases h with h | ⟨h, h'⟩
    · left;  exact add_lt_add_left h _
    · right; exact ⟨by simp; omega, add_le_add_left h' _⟩
  le_of_add_le_add_left := fun a b c h => by
    simp only [Prod.Lex.le_iff] at *
    rcases h with h | ⟨h, h'⟩
    · left;  exact lt_of_add_lt_add_left h
    · right; exact ⟨add_left_cancel h, le_of_add_le_add_left h'⟩

instance instLexWellFoundedLT {α β : Type*} [LT α] [LT β]
    [WellFoundedLT α] [WellFoundedLT β] :
    WellFoundedLT (Lex (α × β)) :=
  ⟨InvImage.wf (fun (p : Lex (α × β)) => (p.1, p.2))
    (WellFounded.prod_lex (wellFounded_lt (α := α)) (wellFounded_lt (α := β)))⟩

/-- The lexicographic order on monomials. -/
def lex : CMonomialOrder σ where
  -- Lean's `Lex` sorts in the reverse order, so we dualize the ordering on σ in constructing Lex.
  syn   := Lex (Π₀ _ : σᵒᵈ, ℕ)
  acm   := instAddCommMonoidLex
  lo    := DFinsupp.Lex.linearOrder
  iocam := DFinsupp.Lex.isOrderedCancelAddMonoid
  wf    := DFinsupp.Lex.wellFoundedLT
  dec   := DFinsupp.Lex.decidableLE
  toSyn := {
    -- Cast the monomial to use dualized indices so Lex starts at the "top"
    toFun      := fun m => toLex (show Π₀ _ : σᵒᵈ, ℕ from m.toFun)
    map_zero'  := toLex_eq_zero.mpr rfl
    map_add'   := fun _ _ => rfl
  }
  toSyn_injective := fun m₁ m₂ h => by
    cases m₁; cases m₂; simp_all

/-- The graded lexicographic order on monomials. -/
def grlex : CMonomialOrder σ where
  -- We augment the lexicographic ordering with the degree.
  syn   := ℕ ×ₗ Lex (Π₀ _ : σᵒᵈ, ℕ)
  acm   := Prod.instAddCommMonoid
  lo    := Prod.Lex.instLinearOrder ℕ (Lex (Π₀ (x : σᵒᵈ), ℕ))
  iocam := sorry
  wf    := sorry
  dec   := Prod.Lex.instDecidableRelOfDecidableEq
  toSyn := {
    toFun     := fun m => (m.degree, toLex (show Π₀ _ : σᵒᵈ, ℕ from m.toFun))
    map_zero' := ofLex_eq_zero.mp rfl
    map_add'  := fun m₁ m₂ => by
      simp [CMonomial.degree_add, CMonomial.toFun_add]; rfl
  }
  toSyn_injective := fun m₁ m₂ h => by
    have h' : toLex m₁.toFun = toLex m₂.toFun := congr_arg Prod.snd h
    cases m₁; cases m₂; simp_all

/-- The graded reverse lexicographic order on monomials. -/
def grevlex : CMonomialOrder σ where
  -- As in `grlex`, we augment the lexicographic ordering with the degree. Here, however, we don't
  -- need to dualize the ordering on `σ` as `Lex` already orders them in the intended manner.
  syn   := ℕ ×ₗ Lex (Π₀ _ : σ, ℕ)ᵒᵈ
  acm   := Prod.instAddCommMonoid
  lo    := Prod.Lex.instLinearOrder ℕ (Lex (Π₀ (x : σ), ℕ))ᵒᵈ
  iocam := sorry
  wf    := sorry
  dec   := sorry
  toSyn := {
    toFun     := fun m => (m.degree, toLex (show Π₀ _ : σᵒᵈ, ℕ from m.toFun))
    map_zero' := ofLex_eq_zero.mp rfl
    map_add'  := fun m₁ m₂ => by
      simp [CMonomial.degree_add, CMonomial.toFun_add]; rfl
  }
  toSyn_injective := fun m₁ m₂ h => by
    have h' : toLex m₁.toFun = toLex m₂.toFun := congr_arg Prod.snd h
    cases m₁; cases m₂; simp_all

end Instances

end CMonomialOrder

namespace CMonomialOrder

set_option linter.unusedSectionVars false

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ] [WellFoundedLT σ]

-- A monomial order is said to be graded if it partitions by degree.
def IsGraded [ord : CMonomialOrder σ] : Prop :=
  ∀ m₁ m₂ : CMonomial σ, m₁.degree < m₂.degree → m₁ ≺[ord] m₂

theorem grlex_isGraded : @IsGraded _ _ (grlex : CMonomialOrder σ) := by
  intros m₁ m₂ h
  change
    toLex (m₁.degree, toLex (show Π₀ _ : σᵒᵈ, ℕ from m₁.toFun))
    < toLex (m₂.degree, toLex (show Π₀ _ : σᵒᵈ, ℕ from m₂.toFun))
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- The grlex order uses the lexicographic order as a tiebreaker. -/
theorem grlex_lt_of_eq_degree_lex_lt (m₁ m₂ : CMonomial σ)
    (h : m₁ ≺[grlex] m₂) (hdeg : m₁.degree = m₂.degree) : m₁ ≺[lex] m₂ := by
  -- The proof state is quite confusing, since both the assumptions and the goal are expressed in
  -- terms of (different) `toSyn`s. Perhaps there is an option that forces the implicit arguments
  -- to be visible.
  change toLex (show Π₀ _ : σᵒᵈ, ℕ from m₁.toFun) < toLex (show Π₀ _ : σᵒᵈ, ℕ from m₂.toFun)
  have h' :
      toLex (m₁.degree, toLex (show Π₀ _ : σᵒᵈ, ℕ from m₁.toFun))
      < toLex (m₂.degree, toLex (show Π₀ _ : σᵒᵈ, ℕ from m₂.toFun)) :=
    h
  -- Ultimately, this is true just by the definition of the lexicographic order on product types.
  rw [Prod.Lex.toLex_lt_toLex] at h'
  rcases h' with h' | ⟨_, h'⟩
  · exact absurd hdeg (Nat.ne_of_lt h')
  · exact h'

end CMonomialOrder

section LeadingMonomial

variable {σ : Type*} [DecidableEq σ] [ord : CMonomialOrder σ]
variable {R : Type*} [DecidableEq R] [CommSemiring R]

namespace CMvPolynomial

/-- The **leading monomial** of a polynomial `f` with respect to a monomial order `ord`. By
    convention, this is typically zero for the zero polynomial but we are good computer scientists
    so we will use the `Option` type. -/
def leadingMonomial (f : CMvPolynomial σ R) : Option (CMonomial σ) :=
  let supp := f.support
  if h : supp.Nonempty then
    some (supp.max' h)
  else
    none

/-- The leading monomial of the zero polynomial is none. -/
lemma leadingMonomial_zero : leadingMonomial (0 : CMvPolynomial σ R) = none := by
  simp [leadingMonomial]; rfl

/-- The leading monomial of a non-zero polynomial is an element of its support. -/
lemma leadingMonomial_eq_some_of_nonempty (f : CMvPolynomial σ R) (hf : f.support.Nonempty) :
    leadingMonomial f = some (f.support.max' hf) := by
  simp [leadingMonomial, hf]

/-- The leading monomial belongs to the support. -/
lemma leadingMonomial_mem_support (f : CMvPolynomial σ R) (hf : f.support.Nonempty) :
    f.support.max' hf ∈ f.support := by
  exact f.support.max'_mem hf

/-- The leading monomial is indeed an upper bound for the support. -/
lemma le_leadingMonomial (f : CMvPolynomial σ R) {m : CMonomial σ} (hm : m ∈ f.support) :
    m ≤ f.support.max' ⟨m, hm⟩ := by
  exact Finset.le_max' _ _ hm

/-- The leading monomial of a single term c * m is just m (when c ≠ 0) -/
lemma leadingMonomial_monomial (m : CMonomial σ) (c : R) (hc : c ≠ 0) :
    leadingMonomial (CMvPolynomial.ofMonomial m c) = some m := by
  rw [leadingMonomial_eq_some_of_nonempty _ (by simp [support_ofMonomial m c hc])]
  simp [support_ofMonomial m c hc, Finset.max'_singleton]

/-- The leading monomial of a product is the product of leading monomials. -/
lemma leadingMonomial_mul' (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
    leadingMonomial (f * g) = (leadingMonomial f).map₂ (· + ·) (leadingMonomial g) := by
  sorry

lemma leadingMonomial_mul (f g : CMvPolynomial σ R) :
    leadingMonomial (f * g) = (leadingMonomial f).map₂ (· + ·) (leadingMonomial g) := by
  by_cases hf : f = 0
  · simp [hf, leadingMonomial_zero]
  by_cases hg : g = 0
  · simp [hg, leadingMonomial_zero]
  exact leadingMonomial_mul' f g hf hg

/-- The leading monomial of a sum is bounded by the larger of the leading
    monomials of the summands. -/
lemma leadingMonomial_add_le' (f g : CMvPolynomial σ R)
    (hf : f.support.Nonempty) (hg : g.support.Nonempty) (hfg : (f + g).support.Nonempty) :
    (f + g).support.max' hfg ≤ max (f.support.max' hf) (g.support.max' hg) :=
  sorry

end CMvPolynomial

end LeadingMonomial
