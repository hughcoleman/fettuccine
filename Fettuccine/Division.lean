import Fettuccine.CMonomialOrder
import Fettuccine.CMvPolynomial

/-!
# Multivariate Polynomial Division

This file defines the division algorithm for `CMvPolynomial σ R` with respect to a monomial order.

## Definitions

* `IsMvQuotientRemainder (tag := tag) f g q r` : the definition of division of `f` by
  `g` producing a quotient `q` and a remainder `r`, i.e. that `f = g * q + r` and that no monomial
  in `r.support` is divisible by `in[ord](g)`.
* `mvDivide (tag := tag) f g hg` : divides `f` by (non-zero) `g` producing a quotient and
  remainder.

## Theorems

* `mvDivide.correct` : the statement that `mvDivide` produces a quotient and remainder satisfying
  `IsMvQuotientRemainder`.
* `mvDivide.unique` : the statement that division is uniquely determined.
-/

namespace CMonomial

variable {σ : Type*} [DecidableEq σ]

/-- The predicate for monomial divisibility. -/
def dvd (m₁ m₂ : CMonomial σ) : Prop :=
  ∀ i ∈ m₁.support, m₁ i ≤ m₂ i

/-- Use the standard divisibility notation for monomials. -/
instance : Dvd (CMonomial σ) where
  dvd := dvd

/-- Divisibility of monomials is decidable. -/
instance (m₁ m₂ : CMonomial σ) : Decidable (m₁ ∣ m₂) := by
  -- `exact Classical.propDecidable (m₁ ∣ m₂)` closes this goal, but is noncomputable. We can
  -- do better by rewriting `∀ i ∈ σ, i ∈ m₁.support → m₁ i ≤ m₂ i` over an explicitly finite set.
  refine decidable_of_iff (∀ i : {i // i ∈ m₁.support}, m₁ i ≤ m₂ i) ?_
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h i
    exact h i i.property

/-- Divide monomials if possible, returning the quotient. -/
def div (m₁ m₂ : CMonomial σ) : Option (CMonomial σ) :=
  if _ : m₂ ∣ m₁ then
    some (m₁ - m₂)
  else
    none

/-- `m₁` is divisible by `m₂` if and only if their quotient is defined (and is their pointwise
    difference). -/
lemma dvd_iff_div_eq {m₁ m₂ : CMonomial σ} : m₂ ∣ m₁ ↔ div m₁ m₂ = some (m₁ - m₂) := by
  constructor
  · intro h; simp [div, h]
  · intro h
    by_cases hdiv : m₂ ∣ m₁
    · exact hdiv
    · have hnone : div m₁ m₂ = none := by
        -- Arguably, we need `not_dvd_iff_div_eq` here!
        simp [div, hdiv]
      simp_all only [reduceCtorEq]

/-- `m₁` is not divisible by `m₂` if and only if their quotient is not defined. -/
lemma not_dvd_iff_div_eq {m₁ m₂ : CMonomial σ} : ¬ m₂ ∣ m₁ ↔ div m₁ m₂ = none := by
  constructor
  · intro h; simp [div, h]
  · intro h hdiv
    have hsome : div m₁ m₂ = some (m₁ - m₂) :=
      (dvd_iff_div_eq).mp hdiv
    simp_all only [reduceCtorEq]

-- The statement that we can quantify over `σ` or `m₁.support` in the definition of `dvd`.
lemma dvd_iff (m₁ m₂ : CMonomial σ) : m₁ ∣ m₂ ↔ ∀ i, m₁ i ≤ m₂ i := by
  constructor
  · intro h i
    by_cases hi : i ∈ m₁.support
    · exact h i hi
    · simp [DFinsupp.notMem_support_iff.mp hi]
  · intro h i hi
    exact h i

/-- The lowest common multiple of two monomials is divisible by its left factor. -/
lemma dvd_lcm_left (m₁ m₂ : CMonomial σ) : m₁ ∣ lcm m₁ m₂ := by
  intro i hi; simp [lcm, DFinsupp.zipWith_apply]

/-- The lowest common multiple of two monomials is divisible by its right factor. -/
lemma dvd_lcm_right (m₁ m₂ : CMonomial σ) : m₂ ∣ lcm m₁ m₂ := by
  intro i hi; simp [lcm, DFinsupp.zipWith_apply]

end CMonomial

open CMonomialOrder
open scoped CMonomialOrder

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [DecidableEq R] [Field R]

namespace CMvPolynomial

variable {tag : Type*} [CMonomialOrder.MonomialOrderTag tag σ]

private abbrev taggedOrder {σ : Type*} [DecidableEq σ]
    {tag : Type*} [CMonomialOrder.MonomialOrderTag tag σ] : CMonomialOrder σ :=
  CMonomialOrder.MonomialOrderTag.ord (tag := tag) (σ := σ)

local notation "ord" => taggedOrder (tag := tag) (σ := σ)

/-- The statement that a given pair of polynomials are a (the) quotient and remainder of a
    particular polynomial division. -/
def IsMvQuotientRemainder (f g q r : CMvPolynomial σ R) : Prop :=
  f = g * q + r ∧ (∀ m ∈ r.support, ¬ in[ord](g) ∣ m)

/-- The support of a difference of two polynomials is contained in the union of the supports of both
    summands. -/
lemma support_sub_subset (f g : CMvPolynomial σ R) : (f - g).support ⊆ f.support ∪ g.support := by
  -- For some reason this needs to be made explicit; `DFinsupp.support_neg` doesn't match. Possibly
  -- because of variable names?
  have hneg : (-g).support = g.support :=
    DFinsupp.support_neg (f := g)
  simpa [sub_eq_add_neg, hneg] using support_add_subset f (-g)

set_option linter.unusedDecidableInType false in
/-- If `R` is a domain, then a polynomial ring over `R` is also a domain. -/
-- Despite the statement, this instance "technically" depends on the underlying choice of monomial
-- order. It would be nice to eliminate this somehow?
@[reducible] def noZeroDivisors : NoZeroDivisors (CMvPolynomial σ R) where
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

-- Instantiate instances of `LinearOrder` and `WellFoundedRelation` on `ord.syn` so that the
-- termination measure for `mvDivide` is interpreted correctly.
local instance : LinearOrder (taggedOrder (tag := tag) (σ := σ)).syn :=
  (taggedOrder (tag := tag) (σ := σ)).lo
local instance : WellFoundedRelation (taggedOrder (tag := tag) (σ := σ)).syn where
  rel := (· < ·)
  wf  := (taggedOrder (tag := tag) (σ := σ)).wf.wf

namespace mvDivide

/-- The metric type for `mvDivide`, which consists of the leading monomial paired with the
    cardinality of its support. -/
abbrev Metric : Type _ := (taggedOrder (tag := tag) (σ := σ)).syn × Nat

/-- The lexicographic relation used by the `mvDivide` termination metric. -/
abbrev MetricRel : Metric (tag := tag) (σ := σ) → Metric (tag := tag) (σ := σ) → Prop :=
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => a₁ < a₂)

/-- The termination metric for `mvDivide`. -/
def metric (f : CMvPolynomial σ R) : Metric (tag := tag) (σ := σ) :=
  ((ord).toSyn in[ord](f), f.support.card)

end mvDivide

/-- If two polynomials have the same leading terms, then their difference has a strictly smaller
    leading term (with respect to the lexicographic measure). -/
private lemma metric_sub_lt_of_same_leadingTerm (f h : CMvPolynomial σ R) (hf : f ≠ 0)
    (hlm : in[ord](h) = in[ord](f))
    (hlc : leadingCoefficient ord h = leadingCoefficient ord f) :
    mvDivide.MetricRel (tag := tag) (mvDivide.metric (tag := tag) (f - h))
      (mvDivide.metric (tag := tag) f) := by
  -- [TO-REVIEW]
  unfold mvDivide.MetricRel mvDivide.metric
  rw [Prod.lex_def]
  have hs : (f - h).support ⊆ f.support ∪ h.support :=
    support_sub_subset (f := f) (g := h)
  have hle : (ord).toSyn in[ord](f - h) ≤ (ord).toSyn in[ord](f) := by
    by_cases hfh : f - h = 0
    · simpa [hfh] using (ord).zero_le in[ord](f)
    · have hmem_sub : in[ord](f - h) ∈ (f - h).support :=
        leadingMonomial_mem_support ord (f - h) hfh
      have hmem_union : in[ord](f - h) ∈ f.support ∪ h.support := hs hmem_sub
      rcases Finset.mem_union.mp hmem_union with hmem_f | hmem_h
      · exact le_leadingMonomial ord f in[ord](f - h) hmem_f
      · exact le_trans
          (le_leadingMonomial ord h in[ord](f - h) hmem_h)
          (by simp [hlm])
  have hcancel : (f - h).coefficientOf in[ord](f) = 0 := by
    calc
      (f - h).coefficientOf in[ord](f)
          = f.coefficientOf in[ord](f) - h.coefficientOf in[ord](f) := by
            simp [CMvPolynomial.coefficientOf]
      _ = leadingCoefficient ord f - leadingCoefficient ord h := by
            simp [CMvPolynomial.leadingCoefficient, CMvPolynomial.coefficientOf, hlm]
      _ = 0 := by
            exact sub_eq_zero.mpr hlc.symm
  by_cases heq : (ord).toSyn in[ord](f - h) = (ord).toSyn in[ord](f)
  · right
    refine ⟨heq, ?_⟩
    have hsub0 : f - h = 0 := by
      by_contra hsub0
      have hmem_sub : in[ord](f - h) ∈ (f - h).support :=
        leadingMonomial_mem_support ord (f - h) hsub0
      have hneq_lm : in[ord](f - h) ≠ in[ord](f) := by
        intro hEq
        have hcoeff_nz : (f - h).coefficientOf in[ord](f) ≠ 0 := by
          simpa [CMvPolynomial.coefficientOf, hEq] using
            (mem_support_iff (f - h) in[ord](f - h)).1 hmem_sub
        exact hcoeff_nz hcancel
      have hneq_syn : (ord).toSyn in[ord](f - h) ≠ (ord).toSyn in[ord](f) := by
        intro hsyn
        exact hneq_lm ((ord).toSyn.injective hsyn)
      exact hneq_syn heq
    have hcard_pos : 0 < f.support.card :=
      Finset.card_pos.mpr ((support_nonempty_iff f).2 hf)
    simpa [hsub0] using hcard_pos
  · left
    exact lt_of_le_of_ne hle heq

/-- Decrease lemma for the `none` branch of `mvDivide`. -/
lemma mvDivide_decreases_none_branch (f g : CMvPolynomial σ R) (hf : f ≠ 0)
  (_hm : CMonomial.div in[ord](f) in[ord](g) = none) :
    mvDivide.MetricRel (tag := tag)
      (mvDivide.metric (tag := tag) (f - leadingTerm ord f))
      (mvDivide.metric (tag := tag) f) := by
  -- [TO-REVIEW]
  have hf_coeff : leadingCoefficient ord f ≠ 0 :=
    CMvPolynomial.leadingCoefficient_ne_zero ord f hf
  have hlm : in[ord](leadingTerm ord f) = in[ord](f) := by
    unfold leadingTerm
    simpa [leadingCoefficient] using
      leadingMonomial_monomial ord in[ord](f) (leadingCoefficient ord f) hf_coeff
  have hlc : leadingCoefficient ord (leadingTerm ord f) = leadingCoefficient ord f := by
    calc
      leadingCoefficient ord (leadingTerm ord f)
          = (leadingTerm ord f).coefficientOf in[ord](leadingTerm ord f) := rfl
      _ = (leadingTerm ord f).coefficientOf in[ord](f) := by rw [hlm]
      _ = leadingCoefficient ord f := by
            change (CMvPolynomial.ofMonomial in[ord](f)
              (leadingCoefficient ord f)).coefficientOf in[ord](f) = leadingCoefficient ord f
            simp [CMvPolynomial.ofMonomial, CMvPolynomial.leadingCoefficient,
              CMvPolynomial.coefficientOf]
  exact metric_sub_lt_of_same_leadingTerm
    f (leadingTerm ord f) hf hlm hlc

/-- Decrease lemma for the `some` branch of `mvDivide`. -/
lemma mvDivide_decreases_some_branch (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0)
    (m : CMonomial σ) (hm : CMonomial.div in[ord](f) in[ord](g) = some m) :
    let c := CMvPolynomial.ofMonomial m (leadingCoefficient ord f / leadingCoefficient ord g)
    mvDivide.MetricRel (tag := tag)
      (mvDivide.metric (tag := tag) (f - c * g))
      (mvDivide.metric (tag := tag) f) := by
  -- [TO-REVIEW]
  classical
  dsimp
  have hf_coeff : leadingCoefficient ord f ≠ 0 :=
    CMvPolynomial.leadingCoefficient_ne_zero ord f hf
  have hg_coeff : leadingCoefficient ord g ≠ 0 :=
    CMvPolynomial.leadingCoefficient_ne_zero ord g hg
  have hdiv : in[ord](g) ∣ in[ord](f) := by
    by_cases h : in[ord](g) ∣ in[ord](f)
    · exact h
    · simp [CMonomial.div, h] at hm
  have hm' : in[ord](f) - in[ord](g) = m := by
    simpa [CMonomial.div, hdiv] using hm
  have hdiv_all : ∀ i, in[ord](g) i ≤ in[ord](f) i :=
    (CMonomial.dvd_iff in[ord](g) in[ord](f)).1 hdiv
  have hmadd : m + in[ord](g) = in[ord](f) := by
    rw [← hm']
    ext i
    exact Nat.sub_add_cancel (hdiv_all i)
  let c : CMvPolynomial σ R :=
    CMvPolynomial.ofMonomial m (leadingCoefficient ord f / leadingCoefficient ord g)
  have hcoeffc : leadingCoefficient ord f / leadingCoefficient ord g ≠ 0 :=
    div_ne_zero hf_coeff hg_coeff
  have hc0 : c ≠ 0 := by
    intro hc
    have hcm : c.coefficientOf m = 0 := by
      simp [CMvPolynomial.coefficientOf, hc]
    have hcm' : c.coefficientOf m = leadingCoefficient ord f / leadingCoefficient ord g := by
      change CMvPolynomial.coefficientOf
          (CMvPolynomial.ofMonomial m (leadingCoefficient ord f / leadingCoefficient ord g)) m =
        leadingCoefficient ord f / leadingCoefficient ord g
      simp [CMvPolynomial.ofMonomial]
    exact hcoeffc (hcm' ▸ hcm)
  have hlm_c : in[ord](c) = m := by
    simpa [c] using
      leadingMonomial_monomial ord m
        (leadingCoefficient ord f / leadingCoefficient ord g) hcoeffc
  have hlm_cg : in[ord](c * g) = in[ord](f) := by
    calc
      in[ord](c * g) = in[ord](c) + in[ord](g) :=
        leadingMonomial_mul ord c g hc0 hg
      _ = m + in[ord](g) := by simp [hlm_c]
      _ = in[ord](f) := hmadd
  have hlc_cg : leadingCoefficient ord (c * g) = leadingCoefficient ord f := by
    have hcoeff_top :
        (c * g).coefficientOf (in[ord](c) + in[ord](g)) =
          c.coefficientOf in[ord](c) * g.coefficientOf in[ord](g) := by
      simpa [CMvPolynomial.leadingCoefficient] using
        leadingCoefficient_mul ord c g hc0 hg
    have hc_eval :
      c.coefficientOf in[ord](c) = leadingCoefficient ord f / leadingCoefficient ord g := by
      rw [hlm_c]
      change CMvPolynomial.coefficientOf
          (CMvPolynomial.ofMonomial m (leadingCoefficient ord f / leadingCoefficient ord g)) m =
        leadingCoefficient ord f / leadingCoefficient ord g
      simp [CMvPolynomial.ofMonomial]
    calc
      leadingCoefficient ord (c * g)
          = (c * g).coefficientOf in[ord](c * g) := rfl
      _ = (c * g).coefficientOf (in[ord](c) + in[ord](g)) := by
            simp [CMvPolynomial.coefficientOf, leadingMonomial_mul ord c g hc0 hg]
      _ = c.coefficientOf in[ord](c) * g.coefficientOf in[ord](g) := hcoeff_top
      _ = (leadingCoefficient ord f / leadingCoefficient ord g) * leadingCoefficient ord g := by
        rw [hc_eval]
        rfl
      _ = leadingCoefficient ord f := by
            simpa [leadingCoefficient] using div_mul_cancel₀ (leadingCoefficient ord f) hg_coeff
  simpa [c] using
    metric_sub_lt_of_same_leadingTerm
      f (c * g) hf hlm_cg hlc_cg

lemma mvDivide_decreases_none_branch' (f g : CMvPolynomial σ R) (hf : f ≠ 0)
  (hm : CMonomial.div in'[ord](f) in'[ord](g) = none) :
    mvDivide.MetricRel (tag := tag)
      (mvDivide.metric (tag := tag) (f - leadingTerm' ord f))
      (mvDivide.metric (tag := tag) f) := by
  have hm_old : CMonomial.div in[ord](f) in[ord](g) = none := by
    simpa only [← leadingMonomial_eq_leadingMonomial' ord f,
      ← leadingMonomial_eq_leadingMonomial' ord g] using hm
  simpa only [← leadingTerm_eq_leadingTerm' ord f] using
    mvDivide_decreases_none_branch (tag := tag) f g hf hm_old

lemma mvDivide_decreases_some_branch' (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0)
    (m : CMonomial σ) (hm : CMonomial.div in'[ord](f) in'[ord](g) = some m) :
    let c := CMvPolynomial.ofMonomial m
      (leadingCoefficient' ord f / leadingCoefficient' ord g)
    mvDivide.MetricRel (tag := tag)
      (mvDivide.metric (tag := tag) (f - c * g))
      (mvDivide.metric (tag := tag) f) := by
  have hm_old : CMonomial.div in[ord](f) in[ord](g) = some m := by
    simpa only [← leadingMonomial_eq_leadingMonomial' ord f,
      ← leadingMonomial_eq_leadingMonomial' ord g] using hm
  simpa only [← leadingCoefficient_eq_leadingCoefficient' ord f,
    ← leadingCoefficient_eq_leadingCoefficient' ord g] using
    mvDivide_decreases_some_branch (tag := tag) f g hf hg m hm_old

set_option linter.unusedVariables false in
/-- The division algorithm for multivariate polynomials. -/
def mvDivide (f g : CMvPolynomial σ R) (hg : g ≠ 0) : CMvPolynomial σ R × CMvPolynomial σ R :=
  if hf : f = 0 then
    (0, 0)
  else
    match hm : CMonomial.div in'[ord](f) in'[ord](g) with
    | some m =>
      -- The leading term is divisible, so we can eliminate it.
      let c      := CMvPolynomial.ofMonomial m
        (f.leadingCoefficient' ord / g.leadingCoefficient' ord)
      let ⟨q, r⟩ := mvDivide (f - c * g) g hg
      (c + q, r)
    | none =>
      -- The leading terms aren't divisible, so move on to the tail of f.
      let lt_f   := leadingTerm' ord f
      let ⟨q, r⟩ := mvDivide (f - lt_f) g hg
      (q, r + lt_f)
termination_by mvDivide.metric (tag := tag) f
decreasing_by
  · exact mvDivide_decreases_some_branch' (tag := tag) f g hf hg m hm
  · exact mvDivide_decreases_none_branch' (tag := tag) f g hf hm

/-- Single-step unfolding of `mvDivide` in the reducing (`some`) branch. -/
private lemma mvDivide_br_reducing (f g : CMvPolynomial σ R) (hg : g ≠ 0) (hf : f ≠ 0)
    (m : CMonomial σ) (hm : CMonomial.div in'[ord](f) in'[ord](g) = some m)
    (c q r : CMvPolynomial σ R)
    (hc : c = CMvPolynomial.ofMonomial m
      (f.leadingCoefficient' ord / g.leadingCoefficient' ord))
    (hqr : mvDivide (tag := tag) (f - c * g) g hg = (q, r)) :
    mvDivide (tag := tag) f g hg = (c + q, r) := by
  rw [mvDivide.eq_def]; aesop

/-- Single-step unfolding of `mvDivide` in the accumulating (`none`) branch. -/
private lemma mvDivide_br_accumulating (f g : CMvPolynomial σ R) (hg : g ≠ 0) (hf : f ≠ 0)
    (hm : CMonomial.div in'[ord](f) in'[ord](g) = none)
    (lt_f q r : CMvPolynomial σ R) (hlt_f : lt_f = leadingTerm' ord f)
    (hqr : mvDivide (tag := tag) (f - lt_f) g hg = (q, r)) :
    mvDivide (tag := tag) f g hg = (q, r + lt_f) := by
  rw [mvDivide.eq_def]; aesop

/-- The results of `mvDivide` satisfy the division relation and remainder constraints. -/
theorem mvDivide_spec (f g : CMvPolynomial σ R) (hg : g ≠ 0) :
    let (q, r) := mvDivide (tag := tag) f g hg
    IsMvQuotientRemainder (tag := tag) f g q r := by
  -- [TO-REVIEW]
  classical
  let motive : CMvPolynomial σ R → Prop := fun x =>
    let (q, r) := mvDivide (tag := tag) x g hg
    IsMvQuotientRemainder (tag := tag) x g q r
  have hmain : ∀ x, motive x := by
    refine mvDivide.induct (tag := tag) g hg (motive := motive) ?_ ?_ ?_
    · have h0 : mvDivide (tag := tag) 0 g hg = (0, 0) := by
        simp [mvDivide.eq_def]
      simp [motive, h0, IsMvQuotientRemainder]
    · intro x hx0 m hm c q r hqr ih
      have ih' : IsMvQuotientRemainder (tag := tag) (x - c * g) g q r := by
        simpa [motive, hqr]
          using ih
      rcases ih' with ⟨hdecomp, hrem⟩
      have hthis : IsMvQuotientRemainder (tag := tag) x g (c + q) r := by
        refine ⟨?_, hrem⟩
        calc
          x = (x - c * g) + c * g := by ring
          _ = (g * q + r) + c * g := by simp [hdecomp]
          _ = g * (c + q) + r     := by ring
      have hstep : mvDivide (tag := tag) x g hg = (c + q, r) := by
        exact mvDivide_br_reducing (tag := tag) x g hg hx0 m hm c q r rfl hqr
      simpa [motive, hstep, c] using hthis
    · intro x hx0 hm lt_f q r hqr ih
      have ih' : IsMvQuotientRemainder (tag := tag) (x - lt_f) g q r := by
        simpa [motive, hqr]
          using ih
      rcases ih' with ⟨hdecomp, hrem⟩
      have hxmem : in[ord](x) ∈ x.support := leadingMonomial_mem_support ord x hx0
      have hxc : leadingCoefficient ord x ≠ 0 := (mem_support_iff x in[ord](x)).1 hxmem
      have hltf_eq_prime : lt_f = leadingTerm' ord x := rfl
      have hltf_eq : lt_f = leadingTerm ord x :=
        hltf_eq_prime.trans (leadingTerm_eq_leadingTerm' ord x).symm
      have hndiv : ¬ in[ord](g) ∣ in[ord](x) := by
        have hm_old :
            CMonomial.div (leadingMonomial ord x) (leadingMonomial ord g) = none := by
          simpa [leadingMonomial_eq_leadingMonomial' ord x,
            leadingMonomial_eq_leadingMonomial' ord g] using hm
        exact (CMonomial.not_dvd_iff_div_eq).2 hm_old
      have hthis : IsMvQuotientRemainder (tag := tag) x g q (r + lt_f) := by
        refine ⟨?_, ?_⟩
        · calc
            x = (x - lt_f) + lt_f := by ring
          _ = (g * q + r) + lt_f := by simp [hdecomp]
            _ = g * q + (r + lt_f) := by ring
        · intro n hn
          have hmem : n ∈ r.support ∪ lt_f.support :=
            support_add_subset (f := r) (g := lt_f) hn
          rcases Finset.mem_union.mp hmem with hr | hlt
          · exact hrem n hr
          · have hsupp_lt : lt_f.support = {in[ord](x)} := by
              rw [hltf_eq, leadingTerm]
              simpa [leadingCoefficient] using
                support_ofMonomial (m := in[ord](x)) (a := leadingCoefficient ord x) hxc
            have hn_eq : n = in[ord](x) := by
              have : n ∈ ({in[ord](x)} : Finset (CMonomial σ)) := by
                simpa [hsupp_lt] using hlt
              simpa using Finset.mem_singleton.mp this
            simpa [hn_eq] using hndiv
      have hstep : mvDivide (tag := tag) x g hg = (q, r + lt_f) := by
        exact mvDivide_br_accumulating (tag := tag) x g hg hx0 hm lt_f q r hltf_eq_prime hqr
      simpa [motive, hstep] using hthis
  simpa [motive] using hmain f

/-- The quotient and remainder of multivariate polynomial division is uniquely determined. -/
theorem mvDivide_unique {f g q₁ q₂ r₁ r₂ : CMvPolynomial σ R} (hg : g ≠ 0)
    (h₁ : IsMvQuotientRemainder (tag := tag) f g q₁ r₁)
    (h₂ : IsMvQuotientRemainder (tag := tag) f g q₂ r₂) :
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
  have hr0 : r₂ - r₁ ≠ 0 := by
    -- We need to bring `NoZeroDivisors` into the context here, because the `noZeroDivisors`
    -- construction requires a monomial order. (FIXME: Use the fact that at least one monomial order
    -- exists, i.e. `lex`, to eliminate this?)
    haveI : NoZeroDivisors (CMvPolynomial σ R) := noZeroDivisors (tag := tag)
    aesop
  have hmem : in[ord](r₂ - r₁) ∈ r₁.support ∪ r₂.support := by
    have hmem' : in[ord](r₂ - r₁) ∈ r₂.support ∪ r₁.support :=
      support_sub_subset (f := r₂) (g := r₁)
        (leadingMonomial_mem_support ord (r₂ - r₁) hr0)
    simpa [Finset.union_comm] using hmem'
  -- In either case, it follows that `g` divides either `r₁` or `r₂`, contradicting the property of
  -- the remainder.
  have hdiv : in[ord](g) ∣ in[ord](r₂ - r₁) := by
    rw [hin, CMonomial.dvd_iff]
    intro i; exact Nat.le_add_right (in[ord](g) i) (in[ord](q₁ - q₂) i)
  rcases Finset.mem_union.mp hmem with hr₁ | hr₂
  · exact (h₁.2 _ hr₁) hdiv
  · exact (h₂.2 _ hr₂) hdiv

end CMvPolynomial
