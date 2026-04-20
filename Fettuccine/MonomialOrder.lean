import Fettuccine.MvPolynomial
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Monomial Orders

This file defines `MonomialOrder`, a structure representing monomial orders on `Monomial σ`, and
provides the lexicographic (lex) monomial order. For the most part, the structure of this file
largely mirrors Mathlib/Data/Finsupp/MonomialOrder.lean.

## Definitions

* `MonomialOrder σ` : a well-founded, translation-invariant total order on `Monomial σ`.
* `MonomialOrder.lex` : the lexicographic order on monomials.
* `MvPolynomial.leadingMonomial` : the leading monomial of a multivariate polynomial with respect
  to a monomial order.

## Notation

* `m₁ ≺[ord] m₂` : strict inequality under the monomial order `ord`.
* `m₁ ≼[ord] m₂` : inequality under the monomial order `ord`.
-/

/-- A **monomial order** on `σ` is a well-founded, translation-invariant (decidable) total order on
    `Monomial σ`. -/
structure MonomialOrder (σ : Type*) [DecidableEq σ] where
  /-- The synonym type from which the order is lifted. -/
  syn : Type*
  /-- `syn` is an additive commutative monoid. -/
  acm : AddCommMonoid syn
  /-- `syn` is linearly ordered. -/
  lo : LinearOrder syn
  /-- `syn` is an additive monoid and cancellative under the linear order. -/
  iocam : IsOrderedCancelAddMonoid syn
  /-- The (additive) equivalence of `Monomial σ` in `syn`. -/
  toSyn : (Monomial σ) ≃+ syn
  /-- `toSyn` is monotone on the pointwise order. -/
  toSyn_monotone : Monotone toSyn.toFun
  /-- `syn` is well-ordered. -/
  wf : WellFoundedLT syn

attribute [instance] MonomialOrder.acm MonomialOrder.lo MonomialOrder.iocam MonomialOrder.wf

namespace MonomialOrder

-- Notation for using the order on the synonym type.
section Notation

/-- Notation for the strict order relation for monomial orders. -/
scoped notation:50 m₁ " ≺[" ord:25 "] " m₂:50 =>
  (MonomialOrder.toSyn ord m₁ < MonomialOrder.toSyn ord m₂)

/-- Notation for the order relation for monomial orders. -/
scoped notation:50 m₁ " ≼[" ord:25 "] " m₂:50 =>
  (MonomialOrder.toSyn ord m₁ ≤ MonomialOrder.toSyn ord m₂)

end Notation

variable {σ : Type*} [DecidableEq σ] (ord : MonomialOrder σ)

/-- Zero is a minimal element of any monomial order. -/
lemma zero_le' (m : ord.syn) : 0 ≤ m := by
  by_contra h; push Not at h
  -- If 0 > m, then by translation-invariance we can construct the infinitely-descending sequence
  -- 0 > m > m² > m³ > ⋯.
  have h' (n : ℕ) : (n + 1) • m < n • m := by
    induction n <;> simpa [one_nsmul, succ_nsmul]
  -- This contradicts the well-foundedness of the order.
  exact WellFounded.not_rel_apply_succ (fun n => (n • m))
    |>.elim (fun n hn => hn (h' n))

-- An instance of `OrderBot`; needed to take a supremum over finite sets of monomials (in the
-- definition of `leadingMonomial`.)
instance : OrderBot ord.syn where
  bot := 0
  bot_le := ord.zero_le'

lemma zero_le (m : Monomial σ) : 0 ≼[ord] m := by
  simp [ord.toSyn.map_zero, zero_le']

-- The order is monotonically increasing.
lemma le_add_right' (m₁ m₂ : ord.syn) : m₁ ≤ m₁ + m₂ := by
  calc m₁ = m₁ + 0   := (add_zero _).symm
       _  ≤ m₁ + m₂  := add_le_add_right (ord.zero_le' m₂) m₁

lemma le_add_right (m₁ m₂ : Monomial σ) : m₁ ≼[ord] m₁ + m₂ := by
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

lemma eq_of_add_eq_of_le {m₁ m₂ m₁' m₂' : Monomial σ}
    (h₁ : m₁' ≼[ord] m₁) (h₂ : m₂' ≼[ord] m₂) (h : m₁' + m₂' = m₁ + m₂) :
    m₁' = m₁ ∧ m₂' = m₂ := by
  rcases ord.eq_of_add_eq_of_le' h₁ h₂
    (by simpa [ord.toSyn.map_add] using congrArg ord.toSyn h) with ⟨h₁', h₂'⟩
  exact ⟨ord.toSyn.injective h₁', ord.toSyn.injective h₂'⟩

/-- A monomial order is **graded** if it respects homogeneity. -/
def IsGraded : Prop :=
  ∀ m₁ m₂ : Monomial σ, m₁.degree < m₂.degree → m₁ ≺[ord] m₂

end MonomialOrder

namespace MonomialOrder

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]

/-- The lexicographic order on monomials. -/
def lex [WellFoundedGT σ] : MonomialOrder σ where
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

end MonomialOrder

section LeadingMonomial

variable {σ : Type*} [DecidableEq σ] (ord : MonomialOrder σ)
variable {R : Type*} [DecidableEq R] [CommSemiring R]

namespace MvPolynomial

/-- The **leading monomial** of a polynomial `f` with respect to a monomial order `ord`. -/
-- The `@[inline]` annotation is necessary: otherwise, Lean unpredictably segfaults when it is
-- asked to evaluate this against the `grlex` or `grevlex` orders (but not the `lex` order,
-- strangely). According to the Agent that spent several hours experimenting, it has something to
-- do with how Lean is forced to funnel through `MonomialOrder` when it is asked to evaluate `<`
-- against a "generic" order. For details, see `MonomialOrderTag` below.
@[inline] def leadingMonomial (f : MvPolynomial σ R) : Monomial σ :=
  ord.toSyn.symm (f.support.sup ord.toSyn)

/-- Notation for the leading monomial of a polynomial under a given monomial order. -/
-- `max` is used to ensure that the notation binds as if it were function application.
scoped notation:max "in[" ord "](" f ")" =>
  (MvPolynomial.leadingMonomial ord f)

/-- The leading monomial of the zero polynomial is zero. -/
@[simp] lemma leadingMonomial_zero : in[ord]((0 : MvPolynomial σ R)) = 0 := by
  simp [leadingMonomial, DirectSum.support_zero]; rfl

/-- The monomials of a polynomial are bounded by the leading monomial. -/
@[simp] lemma le_leadingMonomial (f : MvPolynomial σ R) (m : Monomial σ) (hm : m ∈ f.support) :
    ord.toSyn m ≤ ord.toSyn in[ord](f) := by
  simp only [leadingMonomial, AddEquiv.apply_symm_apply]
  exact Finset.le_sup hm

/-- The leading monomial of a non-zero polynomial is an element of its support. -/
@[simp] lemma leadingMonomial_mem_support (f : MvPolynomial σ R) (hf : f ≠ 0) :
    in[ord](f) ∈ f.support := by
  have hne : f.support.Nonempty := by
    exact (support_nonempty_iff f).mpr hf
  -- Since the polynomial has non-empty support, the supremum is attained, and by the leading
  -- monomial. So in particular, the leading monomial is a member of the support.
  obtain ⟨m, hm, hmsup⟩ := Finset.exists_mem_eq_sup f.support hne ord.toSyn
  rwa [leadingMonomial, hmsup, AddEquiv.symm_apply_apply]

/-- If a ≠ 0, then the leading monomial of the monomial polynomial a*m is m. -/
lemma leadingMonomial_monomial (m : Monomial σ) (a : R) (ha : a ≠ 0) :
    in[ord](MvPolynomial.ofMonomial m a) = m := by
  simp [leadingMonomial, MvPolynomial.support_ofMonomial m a ha]

/-- The leading monomial of a sum is an element of the supports of the summands. -/
lemma leadingMonomial_add_mem (f g : MvPolynomial σ R) (h : f + g ≠ 0) :
    in[ord](f + g) ∈ f.support ∪ g.support := by
  exact (support_add_subset f g) (leadingMonomial_mem_support ord (f + g) h)

/-- The leading monomial of a sum is bounded by the leading monomials of its summands. -/
lemma leadingMonomial_add_le (f g : MvPolynomial σ R) :
    ord.toSyn in[ord](f + g) ≤ max (ord.toSyn in[ord](f)) (ord.toSyn in[ord](g)) := by
  by_cases h : f + g = 0
  · simpa [h] using (ord.zero_le' (max _ _))
  · have hmem : in[ord](f + g) ∈ f.support ∪ g.support := leadingMonomial_add_mem ord f g h
    rcases Finset.mem_union.mp hmem with hf | hg
    · exact le_trans (le_leadingMonomial ord f in[ord](f + g) hf) (le_max_left  _ _)
    · exact le_trans (le_leadingMonomial ord g in[ord](f + g) hg) (le_max_right _ _)

/-- The leading monomial of a product is bounded by the product of the leading monomials. -/
lemma leadingMonomial_mul_le (f g : MvPolynomial σ R) :
    ord.toSyn in[ord](f * g) ≤ ord.toSyn in[ord](f) + ord.toSyn in[ord](g) := by
  -- Expand the leading-monomial expression into a supremum over the support.
  have hsup : ord.toSyn in[ord](f * g) = (f * g).support.sup ord.toSyn := by
    simp [leadingMonomial, AddEquiv.apply_symm_apply]
  -- It suffices to bound each support monomial of `f * g` by the target sum. Any such monomial will
  -- be a sum of monomials in the supports of `f` and `g`.
  refine hsup ▸ Finset.sup_le ?_
  intro m hm
  have hm_image : m ∈ Finset.image₂ (· + ·) f.support g.support :=
    support_mul_subset f g hm
  -- Each sum is bounded by the corresponding leading monomial, so we can add these bounds.
  rcases Finset.mem_image₂.mp hm_image with ⟨m₁, hm₁, m₂, hm₂, hm_add⟩
  calc
    ord.toSyn m = ord.toSyn (m₁ + m₂)                         := by simp [hm_add]
    _           = ord.toSyn m₁ + ord.toSyn m₂                 := ord.toSyn.map_add _ _
    _           ≤ ord.toSyn in[ord](f) + ord.toSyn in[ord](g) :=
                    add_le_add
                      (le_leadingMonomial ord f m₁ hm₁)
                      (le_leadingMonomial ord g m₂ hm₂)

/-- The **leading coefficient** of a polynomial is the coefficient of its leading monomial. -/
@[simp] def leadingCoefficient (f : MvPolynomial σ R) : R :=
  MvPolynomial.coefficientOf f in[ord](f)

/-- A nonzero polynomial has nonzero leading coefficient. -/
lemma leadingCoefficient_ne_zero (f : MvPolynomial σ R) (hf : f ≠ 0) :
    leadingCoefficient ord f ≠ 0 := by
  exact (mem_support_iff f in[ord](f)).mp (leadingMonomial_mem_support ord f hf)

/-- The **leading term** of a polynomial is the leading monomial alongside its coefficient. -/
@[simp] def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  MvPolynomial.ofMonomial in[ord](f) (leadingCoefficient ord f)

/-- The coefficient of the product at the sum of leading monomials is the product of leading
    coefficients. -/
lemma leadingCoefficient_mul (f g : MvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).coefficientOf (in[ord](f) + in[ord](g)) =
      leadingCoefficient ord f * leadingCoefficient ord g := by
  classical
  let s : Finset (Monomial σ × Monomial σ) := f.support ×ˢ g.support
  let n : Monomial σ                        := in[ord](f) + in[ord](g)
  -- Express the product as a sum, as in `support_mul_subset`.
  let termOf : Monomial σ × Monomial σ → MvPolynomial σ R
  | ⟨i, j⟩ => DirectSum.of (fun _ : Monomial σ => R) (i + j)
    (f.coefficientOf i * g.coefficientOf j)
  have mul_eq : f * g = ∑ ij ∈ s, termOf ij := by
    simpa [s, termOf] using (DirectSum.mul_eq_sum_support_ghas_mul _ f g)
  -- Expand the coefficient of `n` in the product `f * g`.
  have h_expand :
      (f * g).coefficientOf n =
        ∑ ⟨i, j⟩ ∈ s, (if i + j = n then
                          f.coefficientOf i * g.coefficientOf j
                        else
                          0) := by
    calc
      (f * g).coefficientOf n
      _ = (∑ ij ∈ s, termOf ij).coefficientOf n := by simp [mul_eq]
      _ = (∑ ij ∈ s, termOf ij) n               := by rfl
      _ = ∑ ij ∈ s, (termOf ij) n               := DFinsupp.finset_sum_apply s termOf n
      _ = ∑ ij ∈ s, (termOf ij).coefficientOf n := by simp [MvPolynomial.coefficientOf]
      _ = ∑ ⟨i, j⟩ ∈ s, (if i + j = n then
                            f.coefficientOf i * g.coefficientOf j
                          else
                            0)                   := by simp [termOf, DirectSum.of_apply]
  -- The only nonzero term in this sum is the one corresponding to the leading monomials of `f` and
  -- `g`. (This is the only term that can possibly contribute to the coefficient at `n`.)
  let i₀ : Monomial σ := in[ord](f)
  let j₀ : Monomial σ := in[ord](g)
  have h_single :
      (∑ ⟨i, j⟩ ∈ s,
          (if i + j = n then
            f.coefficientOf i * g.coefficientOf j
          else
            0))
        = (if i₀ + j₀ = n then
            f.coefficientOf i₀ * g.coefficientOf j₀
          else
            0) := by
    refine Finset.sum_eq_single (s := s)
      (f := fun ⟨i, j⟩ =>
        if i + j = n then
          f.coefficientOf i * g.coefficientOf j
        else
          0)
      (a := (i₀, j₀)) ?_ ?_
    · intro ⟨i, j⟩ _ hij_neq
      by_cases hsum : i + j = n
      · have hsum' : i + j = i₀ + j₀ := by simpa [i₀, j₀, n] using hsum
        have hij_eq : i = i₀ ∧ j = j₀ := by
          refine ord.eq_of_add_eq_of_le ?_ ?_ hsum'
          · exact le_leadingMonomial ord f i (by aesop)
          · exact le_leadingMonomial ord g j (by aesop)
        -- Contradiction, (i₀, j₀) is not equal to itself.
        rcases hij_eq with ⟨rfl, rfl⟩
        exact (hij_neq rfl).elim
      · simp [hsum]
    · intro hij0_nmem
      have hij0_mem : (i₀, j₀) ∈ s := by
        exact Finset.mem_product.mpr
          ⟨by simpa [i₀] using leadingMonomial_mem_support ord f hf,
           by simpa [j₀] using leadingMonomial_mem_support ord g hg⟩
      exact (hij0_nmem hij0_mem).elim
  -- Gluing these equalities together gives the claim.
  rw [h_expand, h_single]
  simp [i₀, j₀, n]

/-- The leading monomial of a product is the sum of the leading monomials. -/
lemma leadingMonomial_mul [NoZeroDivisors R] (f g : MvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
    in[ord](f * g) = in[ord](f) + in[ord](g) := by
  classical
  -- Since we're working in a domain, the leading coefficient of the product is non-zero.
  have hn_mem_supp : in[ord](f) + in[ord](g) ∈ (f * g).support := by
    have hfg_coeff : (f * g).coefficientOf (in[ord](f) + in[ord](g)) ≠ 0 := by
      rw [leadingCoefficient_mul ord f g hf hg]
      refine mul_ne_zero ?_ ?_
      · exact leadingCoefficient_ne_zero ord f hf
      · exact leadingCoefficient_ne_zero ord g hg
    exact (mem_support_iff _ _).mpr hfg_coeff
  -- Now, `leadingMonomial_mul_le` gives us one inequality, so we just need to use the non-vanishing
  -- of the leading coefficient to get the other way.
  have heq : ord.toSyn in[ord](f * g) = ord.toSyn (in[ord](f) + in[ord](g)) := by
    refine le_antisymm ?_ ?_
    · calc
        ord.toSyn in[ord](f * g)
        _ ≤ ord.toSyn in[ord](f) + ord.toSyn in[ord](g) := leadingMonomial_mul_le ord f g
        _ = ord.toSyn (in[ord](f) + in[ord](g))         := (ord.toSyn.map_add _ _).symm
    · exact le_leadingMonomial ord _ _ hn_mem_supp
  exact ord.toSyn.injective heq

end MvPolynomial

end LeadingMonomial

namespace MonomialOrder

universe u v

/-- A type-level tag for a computable monomial order. -/
-- Passing a `MonomialOrder` as a value-level argument causes issues with native evaluation, since
-- it forces the compiler to funnel computation through the projections of `MonomialOrder`. This
-- can cause Lean to segfault. By introducing a type-level "tag" for monomial orders, we can make
-- computations generic over the tag, enabling specialization for concrete orders.
class MonomialOrderTag (tag : Type v) (σ : Type u) [DecidableEq σ] where
  ord : MonomialOrder.{u, u} σ

/-- Type-level tag for lexicographic monomial order. -/
inductive LexOrder : Type where
  | mk

instance lexOrderTag {σ : Type*} [DecidableEq σ] [LinearOrder σ] [WellFoundedGT σ] :
    MonomialOrderTag LexOrder σ where
  ord := lex

end MonomialOrder
