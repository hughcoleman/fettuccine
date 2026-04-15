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

instance : OrderBot ord.syn where
  bot := 0
  bot_le := ord.zero_le'

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
  rcases ord.eq_of_add_eq_of_le' h₁ h₂
    (by simpa [ord.toSyn.map_add] using congrArg ord.toSyn h) with ⟨h₁', h₂'⟩
  exact ⟨ord.toSyn.injective h₁', ord.toSyn.injective h₂'⟩

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

/-- The **leading monomial** of a polynomial `f` with respect to a monomial order `ord`. -/
def leadingMonomial (f : CMvPolynomial σ R) : CMonomial σ :=
  ord.toSyn.symm (f.support.sup ord.toSyn)

/-- Notation for the leading monomial of a polynomial under a given monomial order. -/
-- `max` is used to ensure that the notation binds as if it were function application.
scoped notation:max "in[" ord "](" f ")" =>
  (CMvPolynomial.leadingMonomial ord f)

/-- The leading monomial of the zero polynomial is zero. -/
@[simp] lemma leadingMonomial_zero : in[ord]((0 : CMvPolynomial σ R)) = 0 := by
  simp [leadingMonomial, DirectSum.support_zero]; rfl

/-- The monomials of a polynomial are bounded by the leading monomial. -/
@[simp] lemma le_leadingMonomial (f : CMvPolynomial σ R) (m : CMonomial σ) (hm : m ∈ f.support) :
    ord.toSyn m ≤ ord.toSyn in[ord](f) := by
  simp only [leadingMonomial, AddEquiv.apply_symm_apply]
  exact Finset.le_sup hm

/-- The leading monomial of a non-zero polynomial is an element of its support. -/
@[simp] lemma leadingMonomial_mem_support (f : CMvPolynomial σ R) (hf : f ≠ 0) :
    in[ord](f) ∈ f.support := by
  have hne : f.support.Nonempty := by
    exact (support_nonempty_iff f).mpr hf
  -- Since the polynomial has non-empty support, the supremum is attained, and by the leading
  -- monomial. So in particular, the leading monomial is a member of the support.
  obtain ⟨m, hm, hmsup⟩ := Finset.exists_mem_eq_sup f.support hne ord.toSyn
  rwa [leadingMonomial, hmsup, AddEquiv.symm_apply_apply]

/-- If a ≠ 0, then the leading monomial of the monomial polynomial a*m is m. -/
lemma leadingMonomial_monomial (m : CMonomial σ) (a : R) (ha : a ≠ 0) :
    in[ord](CMvPolynomial.ofMonomial m a) = m := by
  simp [leadingMonomial, CMvPolynomial.support_ofMonomial m a ha]

-- /-- The leading monomial of a sum is bounded by the leading monomials of the summands. -/
-- lemma leadingMonomial_sum_le {ι : Type*} (s : Finset ι) (f : ι → CMvPolynomial σ R) :
--     ord.toSyn in[ord](∑ i ∈ s, f i) ≤ s.sup (fun i => ord.toSyn in[ord](f i)) := by
--   classical
--   -- Unfold the definition: leading monomial = supremum of the support.
--   have lm_eq :
--       ord.toSyn in[ord](∑ i ∈ s, f i) = (∑ i ∈ s, f i).support.sup ord.toSyn := by
--     simp [leadingMonomial, AddEquiv.apply_symm_apply]
--   refine (lm_eq ▸ Finset.sup_le ?_)
--   intro m hm
--   -- A monomial in the sum's support appears in some summand's support.
--   rcases (Finset.mem_biUnion.mp ((CMvPolynomial.support_sum_subset s f) hm)) with ⟨i, hi, hmi⟩
--   calc
--     ord.toSyn m ≤ ord.toSyn in[ord](f i) := le_leadingMonomial ord (f i) m hmi
--     _           ≤ s.sup (fun i => ord.toSyn in[ord](f i)) :=
--                     (Finset.le_sup (s := s) (f := fun i => ord.toSyn in[ord](f i)) hi)

-- lemma leadingMonomial_sum_le₂ (f g : CMvPolynomial σ R) :
--     ord.toSyn in[ord](f + g) ≤ ord.toSyn in[ord](f) ⊔ ord.toSyn in[ord](g) := by
--   classical
--   -- Use a bool-indexed family and apply the previous lemma.
--   let σ : Bool → CMvPolynomial σ R := fun b => if b then f else g
--   simpa [σ, Finset.sum_insert, Finset.sum_singleton, Finset.sup_insert, Finset.sup_singleton]
--     using (leadingMonomial_sum_le ord ({true, false} : Finset Bool) σ)

-- /-- The leading monomial of a product is bounded by the sum of the leading monomials. -/
-- lemma leadingMonomial_mul_le₂ (f g : CMvPolynomial σ R) :
--     ord.toSyn in[ord](f * g) ≤ ord.toSyn in[ord](f) + ord.toSyn in[ord](g) := by
--   classical
--   have lm_eq : ord.toSyn in[ord](f * g) = (f * g).support.sup ord.toSyn := by
--     simp [leadingMonomial, AddEquiv.apply_symm_apply]
--   -- Reduce to bounding each support monomial of the product.
--   refine (lm_eq ▸ (Finset.sup_le (s := (f * g).support) (f := fun m => ord.toSyn m)) ?_)
--   intro m hm
--   -- Any product monomial is a sum of support monomials from f and g.
--   have hm' : m ∈ Finset.image₂ (· + ·) f.support g.support := by
--     exact (CMvPolynomial.support_mul_subset f g) hm
--   rcases (Finset.mem_image₂.mp hm') with ⟨m₁, hm₁, m₂, hm₂, rfl⟩
--   have h₁ : ord.toSyn m₁ ≤ ord.toSyn in[ord](f) := le_leadingMonomial ord f m₁ hm₁
--   have h₂ : ord.toSyn m₂ ≤ ord.toSyn in[ord](g) := le_leadingMonomial ord g m₂ hm₂
--   simpa [ord.toSyn.map_add] using add_le_add h₁ h₂

/-- The **leading coefficient** of a polynomial is the coefficient of its leading monomial. -/
def leadingCoefficient (f : CMvPolynomial σ R) : R :=
  f in[ord](f)

/-- The **leading term** of a polynomial is the leading monomial alongside its coefficient. -/
def leadingTerm (f : CMvPolynomial σ R) : CMvPolynomial σ R :=
  CMvPolynomial.ofMonomial in[ord](f) (leadingCoefficient ord f)

end CMvPolynomial

end LeadingMonomial
