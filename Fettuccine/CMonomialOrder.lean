import Fettuccine.CMvPolynomial
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finset.Sort

/-!
# CMonomial Orders

This file defines `CMonomialOrder`, a structure representing monomial orders on `CMonomial σ`, and
provides the lexicographic (lex) monomial order. For the most part, the structure of this file
largely mirrors Mathlib/Data/Finsupp/CMonomialOrder.lean.

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
  bot    := 0
  bot_le := ord.zero_le'

lemma zero_le (m : CMonomial σ) : 0 ≼[ord] m := by
  simp [ord.toSyn.map_zero, zero_le']

-- The order is monotonically increasing.
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
-- The `@[inline]` annotation is necessary: otherwise, Lean unpredictably segfaults when it is
-- asked to evaluate this against the `grlex` or `grevlex` orders (but not the `lex` order,
-- strangely). Seemingly this has to do with how Lean optimizes the evaluation of this definition,
-- but it's difficult to say.
@[inline] def leadingMonomial (f : CMvPolynomial σ R) : CMonomial σ :=
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

/-- The leading monomial of a sum is an element of the supports of the summands. -/
lemma leadingMonomial_add_mem (f g : CMvPolynomial σ R) (h : f + g ≠ 0) :
    in[ord](f + g) ∈ f.support ∪ g.support := by
  exact (support_add_subset f g) (leadingMonomial_mem_support ord (f + g) h)

/-- The leading monomial of a sum is bounded by the leading monomials of its summands. -/
lemma leadingMonomial_add_le (f g : CMvPolynomial σ R) :
    ord.toSyn in[ord](f + g) ≤ max (ord.toSyn in[ord](f)) (ord.toSyn in[ord](g)) := by
  by_cases h : f + g = 0
  · simpa [h] using (ord.zero_le' (max _ _))
  · have hmem : in[ord](f + g) ∈ f.support ∪ g.support := leadingMonomial_add_mem ord f g h
    rcases Finset.mem_union.mp hmem with hf | hg
    · exact le_trans (le_leadingMonomial ord f in[ord](f + g) hf) (le_max_left  _ _)
    · exact le_trans (le_leadingMonomial ord g in[ord](f + g) hg) (le_max_right _ _)

/-- The leading monomial of a product is bounded by the product of the leading monomials. -/
lemma leadingMonomial_mul_le (f g : CMvPolynomial σ R) :
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
@[simp] def leadingCoefficient (f : CMvPolynomial σ R) : R :=
  CMvPolynomial.coefficientOf f in[ord](f)

/-- A nonzero polynomial has nonzero leading coefficient. -/
lemma leadingCoefficient_ne_zero (f : CMvPolynomial σ R) (hf : f ≠ 0) :
    leadingCoefficient ord f ≠ 0 := by
  exact (mem_support_iff f in[ord](f)).mp (leadingMonomial_mem_support ord f hf)

/-- The **leading term** of a polynomial is the leading monomial alongside its coefficient. -/
@[simp] def leadingTerm (f : CMvPolynomial σ R) : CMvPolynomial σ R :=
  CMvPolynomial.ofMonomial in[ord](f) (leadingCoefficient ord f)

/-- The coefficient of the product at the sum of leading monomials is the product of leading
    coefficients. -/
lemma leadingCoefficient_mul (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).coefficientOf (in[ord](f) + in[ord](g)) =
      leadingCoefficient ord f * leadingCoefficient ord g := by
  classical
  let s : Finset (CMonomial σ × CMonomial σ) := f.support ×ˢ g.support
  let n : CMonomial σ                        := in[ord](f) + in[ord](g)
  -- Express the product as a sum, as in `support_mul_subset`.
  let termOf : CMonomial σ × CMonomial σ → CMvPolynomial σ R
  | ⟨i, j⟩ => DirectSum.of (fun _ : CMonomial σ => R) (i + j)
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
      _ = ∑ ij ∈ s, (termOf ij).coefficientOf n := by simp [CMvPolynomial.coefficientOf]
      _ = ∑ ⟨i, j⟩ ∈ s, (if i + j = n then
                            f.coefficientOf i * g.coefficientOf j
                          else
                            0)                   := by simp [termOf, DirectSum.of_apply]
  -- The only nonzero term in this sum is the one corresponding to the leading monomials of `f` and
  -- `g`. (This is the only term that can possibly contribute to the coefficient at `n`.)
  let i₀ : CMonomial σ := in[ord](f)
  let j₀ : CMonomial σ := in[ord](g)
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
        -- Contradiction; we get that (i₀, j₀) is not equal to itself.
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
lemma leadingMonomial_mul [NoZeroDivisors R] (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
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

/-- The **sorted support** of a multivariate polynomial, according to a given monomial order. -/
@[inline] def supportSorted (f : CMvPolynomial σ R) : List (CMonomial σ) :=
  let rel : CMonomial σ → CMonomial σ → Prop :=
    fun m₁ m₂ => ord.toSyn m₁ ≤ ord.toSyn m₂
  letI : Std.Total rel :=
    ⟨fun x y => le_total (ord.toSyn x) (ord.toSyn y)⟩
  letI : Std.Antisymm rel :=
    ⟨fun _ _ hxy hyx => ord.toSyn.injective (le_antisymm hxy hyx)⟩
  letI : IsTrans (CMonomial σ) rel :=
    ⟨fun _ _ _ hxy hyz => le_trans hxy hyz⟩
  f.support.sort rel

/-- The sorted support of a multivariate polynomial is nil if and only if the polynomial is zero. -/
lemma supportSorted_eq_nil_iff_zero (f : CMvPolynomial σ R) :
    supportSorted ord f = [] ↔ f = 0 := by
  classical
  -- Establish the relation and its structure.
  let rel : CMonomial σ → CMonomial σ → Prop :=
    fun m₁ m₂ => ord.toSyn m₁ ≤ ord.toSyn m₂
  letI : Std.Total rel :=
    ⟨fun x y => le_total (ord.toSyn x) (ord.toSyn y)⟩
  letI : Std.Antisymm rel :=
    ⟨fun _ _ hxy hyx => ord.toSyn.injective (le_antisymm hxy hyx)⟩
  letI : IsTrans (CMonomial σ) rel :=
    ⟨fun _ _ _ hxy hyz => le_trans hxy hyz⟩
  constructor
  · intro h
    ext m
    -- If the polynomial is not the zero polynomial, then there is a monomial whose coefficient
    -- is non-zero. This monomial is in the support, and hence in the sorted support.
    by_contra hm
    have hm_support : m ∈ f.support :=
      (mem_support_iff f m).mpr hm
    have hm_ssupport : m ∈ supportSorted ord f := by
      unfold supportSorted
      apply (Finset.mem_sort (s := f.support) rel).mpr
      assumption
    simp [h] at hm_ssupport
  -- The converse is much easier.
  · intro h; simp [supportSorted, h]

/-- The sorted support of a multivariate polynomial is empty if and only if the support of the
    polynomial is the empty set. -/
lemma supportSorted_eq_nil_iff_support_eq_empty (f : CMvPolynomial σ R) :
    supportSorted ord f = [] ↔ f.support = ∅ := by
  rw [supportSorted_eq_nil_iff_zero, DFinsupp.support_eq_empty]
  rfl

/-- A computation-friendly leading monomial, defined as the last element of the sorted support. -/
@[inline] def leadingMonomial' (f : CMvPolynomial σ R) : CMonomial σ :=
  (supportSorted ord f).getLast?.getD 0

/-- The sorted-support leading monomial agrees with the `Finset.sup` definition. -/
theorem leadingMonomial_eq_leadingMonomial' (f : CMvPolynomial σ R) :
    leadingMonomial ord f = leadingMonomial' ord f := by
  classical
  -- Establish the relation and its structure.
  let rel : CMonomial σ → CMonomial σ → Prop :=
    fun m₁ m₂ => ord.toSyn m₁ ≤ ord.toSyn m₂
  letI : Std.Total rel :=
    ⟨fun x y => le_total (ord.toSyn x) (ord.toSyn y)⟩
  letI : Std.Antisymm rel :=
    ⟨fun _ _ hxy hyx => ord.toSyn.injective (le_antisymm hxy hyx)⟩
  letI : IsTrans (CMonomial σ) rel :=
    ⟨fun _ _ _ hxy hyz => le_trans hxy hyz⟩
  -- If `supportSorted` is empty, then we know `f` has empty support, and so in both cases the
  -- leading monomial is zero.
  by_cases hl : supportSorted ord f = []
  · have hsupp : f.support = ∅ := by
      exact (supportSorted_eq_nil_iff_support_eq_empty ord f).mp hl
    apply ord.toSyn.injective
    simp [leadingMonomial, leadingMonomial', hl, hsupp]
    rfl
  -- Otherwise, we'll argue two inequalities (under toSyn), which can be pulled back by injectivity.
  · have hsup_ge : ord.toSyn ((supportSorted ord f).getLast hl) ≤ f.support.sup ord.toSyn := by
      have h : (supportSorted ord f).getLast hl ∈ f.support :=
        (Finset.mem_sort fun m₁ m₂ ↦ ord.toSyn m₁ ≤ ord.toSyn m₂).mp (List.getLast_mem hl)
      exact Finset.le_sup h
    have hsup_le : f.support.sup ord.toSyn ≤ ord.toSyn ((supportSorted ord f).getLast hl) := by
      refine Finset.sup_le ?_
      intro m hm
      have hm_ssupport : m ∈ supportSorted ord f := by
        unfold supportSorted
        apply (Finset.mem_sort (s := f.support) rel).mpr
        assumption
      -- Since `supportSorted` is sorted, the last element is an upper bound on all elements, which
      -- is exactly what we are trying to prove.
      have hrel : (supportSorted ord f).Pairwise rel := by
        simp [supportSorted, rel]
      exact hrel.rel_getLast hm_ssupport
    -- Pulling these inequalities back along `ord.toSyn` provides the equality.
    apply ord.toSyn.injective
    calc
      ord.toSyn (leadingMonomial ord f)
      _ = f.support.sup ord.toSyn                      := by simp [leadingMonomial]
      _ = ord.toSyn ((supportSorted ord f).getLast hl) := le_antisymm hsup_le hsup_ge
      _ = ord.toSyn (leadingMonomial' ord f)           := by
            simp [leadingMonomial', hl, List.getLast?_eq_getLast_of_ne_nil]

/-- Notation for the leading monomial of a polynomial under a given monomial order. -/
-- As above, the `max` priority is used so that this binds like function application.
scoped notation:max "in'[" ord "](" f ")" =>
  (CMvPolynomial.leadingMonomial' ord f)

/-- The leading coefficient of a multivariate polynomial, computed via `leadingMonomial'`. -/
@[inline] def leadingCoefficient' (f : CMvPolynomial σ R) : R :=
  CMvPolynomial.coefficientOf f in'[ord](f)

theorem leadingCoefficient_eq_leadingCoefficient' (f : CMvPolynomial σ R) :
    leadingCoefficient ord f = leadingCoefficient' ord f := by
  simp [leadingCoefficient, leadingCoefficient', leadingMonomial_eq_leadingMonomial' ord f]

/-- The leading term of a multivariate polynomial, computed via `leadingMonomial'`. -/
@[inline] def leadingTerm' (f : CMvPolynomial σ R) : CMvPolynomial σ R :=
  CMvPolynomial.ofMonomial in'[ord](f) (leadingCoefficient' ord f)

theorem leadingTerm_eq_leadingTerm' (f : CMvPolynomial σ R) :
    leadingTerm ord f = leadingTerm' ord f := by
  simp [leadingTerm, leadingTerm', leadingMonomial_eq_leadingMonomial' ord f, leadingCoefficient']

end CMvPolynomial

end LeadingMonomial

namespace CMonomialOrder

universe u v

/-- A type-level tag for a computable monomial order. -/
-- This allows monomial orders to be passed implicitly, via typeclass inference.
--
-- Admittedly, this is a relic of when we thought that the cause of Lean's segfaults had something
-- to do with the fact that our procedures were not being monomorphized over the monomial order
-- `ord`. (This is proven to be wrong; hard-coding the order still fails.)
class MonomialOrderTag (tag : Type v) (σ : Type u) [DecidableEq σ] where
  ord : CMonomialOrder.{u, u} σ

/-- Type-level tag for lexicographic monomial order. -/
inductive LexOrder : Type where
  | mk

instance lexOrderTag {σ : Type*} [DecidableEq σ] [LinearOrder σ] [WellFoundedGT σ] :
    MonomialOrderTag LexOrder σ where
  ord := lex

end CMonomialOrder

namespace CMvPolynomial

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [DecidableEq R] [CommRing R]

open CMonomialOrder

set_option linter.unusedDecidableInType false in
/-- If `R` is a domain, then a polynomial ring over `R` is also a domain. -/
-- This proof requires a monomial order to be supplied, because it relies on the fact that the
-- leading term of a product is the product of the leading terms. Unfortunately, Lean isn't able to
-- see that this doesn't depend on the concrete choice of order.
@[reducible] def noZeroDivisorsOfMonomialOrder (ord : CMonomialOrder σ) [NoZeroDivisors R] :
    NoZeroDivisors (CMvPolynomial σ R) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    -- We can assume a ≠ 0 and b ≠ 0, because otherwise the conclusion is trivial.
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    -- Proceed by contradiction. In a nutshell, we're arguing that the leading term of `a * b` is
    -- the product of the leading terms of `a` and `b`, and so we can pass to the fact that `R` is
    -- a domain.
    exfalso
    have hzero : a.leadingCoefficient ord * b.leadingCoefficient ord = 0 := by
      calc
        a.leadingCoefficient ord * b.leadingCoefficient ord
        _ = (a * b).coefficientOf (in[ord](a) + in[ord](b))
              := by exact (leadingCoefficient_mul ord a b ha hb).symm
        _ = 0 := by simp [h]
    exact (mul_ne_zero
      (CMvPolynomial.leadingCoefficient_ne_zero ord a ha)
      (CMvPolynomial.leadingCoefficient_ne_zero ord b hb)) hzero

variable [LinearOrder σ] [WellFoundedGT σ]

set_option linter.unusedDecidableInType false in
/-- If `R` is a domain, then a polynomial ring over `R` is also a domain. -/
instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors (CMvPolynomial σ R) :=
  noZeroDivisorsOfMonomialOrder lex

end CMvPolynomial
