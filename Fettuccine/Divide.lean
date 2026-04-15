import Fettuccine.CMonomialOrder
import Fettuccine.CMvPolynomial
import Mathlib.Algebra.DirectSum.Internal

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

/-- The statement that a given pair of polynomials are the quotient and remainder of a particular
    polynomial division. -/
def IsMvQuotientRemainder (f g q r : CMvPolynomial σ R) : Prop :=
  f = g * q + r ∧ (∀ m ∈ r.support, ¬ CMonomial.divides? in[ord](g) m)

/-- The coefficient of the product at the sum of leading monomials is the product of leading
    coefficients. -/
lemma coeff_mul_leadingMonomial_add (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g) (in[ord](f) + in[ord](g)) = f in[ord](f) * g in[ord](g) := by
  have hfmem : in[ord](f) ∈ f.support := leadingMonomial_mem_support (ord := ord) f hf
  have hgmem : in[ord](g) ∈ g.support := leadingMonomial_mem_support (ord := ord) g hg
  rw [DirectSum.mul_eq_sum_support_ghas_mul
    (A := fun _ : CMonomial σ => R) (a := f) (a' := g)]
  change
    (∑ ij ∈ f.support ×ˢ g.support,
        (DirectSum.of (fun _ : CMonomial σ => R) (ij.1 + ij.2) (f ij.1 * g ij.2)))
      (in[ord](f) + in[ord](g)) = f in[ord](f) * g in[ord](g)
  let s : Finset (CMonomial σ × CMonomial σ) := f.support ×ˢ g.support
  let term : CMonomial σ × CMonomial σ → CMvPolynomial σ R :=
    fun ij => DirectSum.of (fun _ : CMonomial σ => R) (ij.1 + ij.2) (f ij.1 * g ij.2)
  let n : CMonomial σ := in[ord](f) + in[ord](g)
  have h_expand1 : (∑ ij ∈ s, term ij) n = ∑ ij ∈ s, (term ij) n := by
    exact DFinsupp.finset_sum_apply (s := s) (g := term) (i := n)
  have h_expand2 :
      (∑ ij ∈ s, (term ij) n)
        = ∑ ij ∈ s, (if ij.1 + ij.2 = n then (f ij.1 * g ij.2 : R) else 0) := by
    simp [term, n, DirectSum.of_apply]
  have h_expand :
      (∑ ij ∈ f.support ×ˢ g.support,
          (DirectSum.of (fun _ : CMonomial σ => R) (ij.1 + ij.2) (f ij.1 * g ij.2)))
        (in[ord](f) + in[ord](g))
        = ∑ ij ∈ s, (if ij.1 + ij.2 = n then (f ij.1 * g ij.2 : R) else 0) := by
    simpa [s, term, n] using h_expand1.trans h_expand2
  rw [h_expand]
  have hsingle :
      (∑ ij ∈ s, (if ij.1 + ij.2 = n then (f ij.1 * g ij.2 : R) else 0))
        = (if (in[ord](f), in[ord](g)).1 + (in[ord](f), in[ord](g)).2 = n
            then (f (in[ord](f), in[ord](g)).1 * g (in[ord](f), in[ord](g)).2 : R)
            else 0) := by
    refine Finset.sum_eq_single
        (s := s)
        (f := fun ij => if ij.1 + ij.2 = n then (f ij.1 * g ij.2 : R) else 0)
        (a := (in[ord](f), in[ord](g))) ?_ ?_
    · intro ij hij hneq
      by_cases hij_sum : ij.1 + ij.2 = n
      · have hij_mem : ij ∈ f.support ×ˢ g.support := by simpa [s] using hij
        have hij_sum' : ij.1 + ij.2 = in[ord](f) + in[ord](g) := by simpa [n] using hij_sum
        have hij₁_mem : ij.1 ∈ f.support := (Finset.mem_product.mp hij_mem).1
        have hij₂_mem : ij.2 ∈ g.support := (Finset.mem_product.mp hij_mem).2
        have hij₁_le : ij.1 ≼[ord] in[ord](f) :=
          le_leadingMonomial (ord := ord) f ij.1 hij₁_mem
        have hij₂_le : ij.2 ≼[ord] in[ord](g) :=
          le_leadingMonomial (ord := ord) g ij.2 hij₂_mem
        have hij_eq : ij.1 = in[ord](f) ∧ ij.2 = in[ord](g) :=
          ord.eq_of_add_eq_of_le hij₁_le hij₂_le hij_sum'
        have : ij = (in[ord](f), in[ord](g)) := Prod.ext hij_eq.1 hij_eq.2
        exact (hneq this).elim
      · simp [hij_sum]
    · intro hnot
      have hpairmem : (in[ord](f), in[ord](g)) ∈ f.support ×ˢ g.support :=
        Finset.mem_product.mpr ⟨hfmem, hgmem⟩
      exfalso
      exact hnot (by simpa [s] using hpairmem)
  simpa [n] using hsingle

/-- The leading monomial of a product is the product of the leading monomials. -/
lemma leadingMonomial_mul (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
    in[ord](f * g) = in[ord](f) + in[ord](g) := by
  classical
  -- One direction holds even when `R` is not a domain; we can lift this from `CMonomialOrder.lean`.
  have hle : ord.toSyn in[ord](f * g) ≤ ord.toSyn in[ord](f) + ord.toSyn in[ord](g) :=
    leadingMonomial_mul_le (ord := ord) f g
  -- Lower bound: the product of the two leading monomials occurs in `f * g`.
  have hmem_top : in[ord](f) + in[ord](g) ∈ (f * g).support := by
    have hfmem : in[ord](f) ∈ f.support := leadingMonomial_mem_support (ord := ord) f hf
    have hgmem : in[ord](g) ∈ g.support := leadingMonomial_mem_support (ord := ord) g hg
    have hfcoeff : f in[ord](f) ≠ 0 := (mem_support_iff f in[ord](f)).1 hfmem
    have hgcoeff : g in[ord](g) ≠ 0 := (mem_support_iff g in[ord](g)).1 hgmem
    have hcoeff_top := coeff_mul_leadingMonomial_add (ord := ord) f g hf hg
    have hfgcoeff : (f * g) (in[ord](f) + in[ord](g)) ≠ 0 := by
      rw [hcoeff_top]
      exact mul_ne_zero hfcoeff hgcoeff
    exact (mem_support_iff (f * g) (in[ord](f) + in[ord](g))).2 hfgcoeff
  have hge : ord.toSyn in[ord](f) + ord.toSyn in[ord](g) ≤ ord.toSyn in[ord](f * g) := by
    have htop : ord.toSyn (in[ord](f) + in[ord](g)) ≤ ord.toSyn in[ord](f * g) :=
      le_leadingMonomial (ord := ord) (f * g) (in[ord](f) + in[ord](g)) hmem_top
    simpa [ord.toSyn.map_add] using htop
  have hsyn : ord.toSyn in[ord](f * g) = ord.toSyn in[ord](f) + ord.toSyn in[ord](g) :=
    le_antisymm hle hge
  exact ord.toSyn.injective (by simpa [ord.toSyn.map_add] using hsyn)

/-- If `R` is nontrivial, then a polynomial ring over `R` is also non-trivial. -/
instance nontrivial : Nontrivial (CMvPolynomial σ R) where
  exists_pair_ne := by
    -- Lift distinct elements of `R` to distinct constant polynomials.
    obtain ⟨a, b, hxy⟩ := exists_pair_ne R
    refine ⟨CMvPolynomial.C a, CMvPolynomial.C b, ?_⟩
    intro hC
    apply hxy
    exact congrArg (fun p : CMvPolynomial σ R => p 0) hC

set_option linter.unusedDecidableInType false in
/-- If `R` is a domain, then a polynomial ring over `R` is also a domain. -/
instance noZeroDivisors : NoZeroDivisors (CMvPolynomial σ R) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    exfalso
    have hcoeff : (a * b) (in[ord](a) + in[ord](b)) = a in[ord](a) * b in[ord](b) :=
      coeff_mul_leadingMonomial_add (ord := ord) a b ha hb
    have ha_mem : in[ord](a) ∈ a.support := leadingMonomial_mem_support (ord := ord) a ha
    have hb_mem : in[ord](b) ∈ b.support := leadingMonomial_mem_support (ord := ord) b hb
    have ha_coeff : a in[ord](a) ≠ 0 := (mem_support_iff a in[ord](a)).1 ha_mem
    have hb_coeff : b in[ord](b) ≠ 0 := (mem_support_iff b in[ord](b)).1 hb_mem
    have hzero : (a * b) (in[ord](a) + in[ord](b)) = 0 := by simp [h]
    rw [hcoeff] at hzero
    exact (mul_ne_zero ha_coeff hb_coeff) hzero

-- Orderings on monomials, made explicit for termination.
local instance : LinearOrder ord.syn := ord.lo

local instance : WellFoundedRelation ord.syn where
  rel := (· < ·)
  wf  := ord.wf.wf

/-- If two polynomials have the same leading monomial and leading coefficient, then subtracting
    one from the other decreases with respect to the lexicographic measure. -/
lemma terminationMeasure_sub_strict_of_same_leadingData (f h : CMvPolynomial σ R) (hf : f ≠ 0)
    (hlm : in[ord](h) = in[ord](f))
    (hlc : leadingCoefficient ord h = leadingCoefficient ord f) :
    Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => a₁ < a₂)
      (ord.toSyn in[ord](f - h), (f - h).support.card)
      (ord.toSyn in[ord](f)    ,       f.support.card) := by
  rw [Prod.lex_def]
  have hs : (f - h).support ⊆ f.support ∪ h.support := by
    have hneg : (-h).support = h.support := DFinsupp.support_neg (f := h)
    simpa [sub_eq_add_neg, hneg] using
      (support_add_subset (f := f) (g := -h))
  have hle : ord.toSyn in[ord](f - h) ≤ ord.toSyn in[ord](f) := by
    by_cases hfh : f - h = 0
    · simpa [hfh] using ord.zero_le in[ord](f)
    · have hmem_sub : in[ord](f - h) ∈ (f - h).support :=
        leadingMonomial_mem_support (ord := ord) (f - h) hfh
      have hmem_union : in[ord](f - h) ∈ f.support ∪ h.support := hs hmem_sub
      rcases Finset.mem_union.mp hmem_union with hmem_f | hmem_h
      · exact le_leadingMonomial (ord := ord) f in[ord](f - h) hmem_f
      · exact le_trans
          (le_leadingMonomial (ord := ord) h in[ord](f - h) hmem_h)
          (by simp [hlm])
  have hcancel : (f - h) in[ord](f) = 0 := by
    calc
      (f - h) in[ord](f) = f in[ord](f) - h in[ord](f) := by simp
      _ = leadingCoefficient ord f - leadingCoefficient ord h := by
            simp [leadingCoefficient, hlm]
      _ = 0 := by simp [hlc]
  by_cases heq : ord.toSyn in[ord](f - h) = ord.toSyn in[ord](f)
  · right
    refine ⟨heq, ?_⟩
    have hsub0 : f - h = 0 := by
      by_contra hsub0
      have hmem_sub : in[ord](f - h) ∈ (f - h).support :=
        leadingMonomial_mem_support (ord := ord) (f - h) hsub0
      have hneq_lm : in[ord](f - h) ≠ in[ord](f) := by
        intro hEq
        have hcoeff_nz : (f - h) in[ord](f) ≠ 0 := by
          simpa [hEq] using (mem_support_iff (f - h) in[ord](f - h)).1 hmem_sub
        exact hcoeff_nz hcancel
      have hneq_syn : ord.toSyn in[ord](f - h) ≠ ord.toSyn in[ord](f) := by
        intro hsyn
        exact hneq_lm (ord.toSyn.injective hsyn)
      exact hneq_syn heq
    have hcard_pos : 0 < f.support.card :=
      Finset.card_pos.mpr ((support_nonempty_iff f).2 hf)
    simpa [hsub0] using hcard_pos
  · left
    exact lt_of_le_of_ne hle heq

/-- Decrease lemma for the `none` branch of `mvDivide`. -/
lemma mvDivide_decreases_none_branch (f g : CMvPolynomial σ R) (hf : f ≠ 0)
  (_hm : CMonomial.divide in[ord](f) in[ord](g) = none) :
    Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => a₁ < a₂)
      (ord.toSyn in[ord](f - leadingTerm ord f), (f - leadingTerm ord f).support.card)
      (ord.toSyn in[ord](f)                    ,                       f.support.card) := by
  have hfmem : in[ord](f) ∈ f.support := leadingMonomial_mem_support (ord := ord) f hf
  have hfcoeff : leadingCoefficient ord f ≠ 0 := (mem_support_iff f in[ord](f)).1 hfmem
  have hlm : in[ord](leadingTerm ord f) = in[ord](f) := by
    unfold leadingTerm
    simpa [leadingCoefficient] using
      leadingMonomial_monomial (ord := ord) in[ord](f) (leadingCoefficient ord f) hfcoeff
  have hlc : leadingCoefficient ord (leadingTerm ord f) = leadingCoefficient ord f := by
    calc
      leadingCoefficient ord (leadingTerm ord f)
          = (leadingTerm ord f) in[ord](leadingTerm ord f) := rfl
      _ = (leadingTerm ord f) in[ord](f) := by simp [hlm]
      _ = leadingCoefficient ord f := by
            change (CMvPolynomial.ofMonomial in[ord](f) (leadingCoefficient ord f)) in[ord](f)
              = leadingCoefficient ord f
            simp [CMvPolynomial.ofMonomial]
  exact terminationMeasure_sub_strict_of_same_leadingData
    (ord := ord) f (leadingTerm ord f) hf hlm hlc

/-- Decrease lemma for the `some` branch of `mvDivide`. -/
lemma mvDivide_decreases_some_branch (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0)
    (m : CMonomial σ) (hm : CMonomial.divide in[ord](f) in[ord](g) = some m) :
    let c := CMvPolynomial.ofMonomial m (leadingCoefficient ord f / leadingCoefficient ord g)
    Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => a₁ < a₂)
      (ord.toSyn in[ord](f - c * g), (f - c * g).support.card)
      (ord.toSyn in[ord](f)        ,           f.support.card) := by
  classical
  dsimp
  have hfmem : in[ord](f) ∈ f.support := leadingMonomial_mem_support (ord := ord) f hf
  have hgmem : in[ord](g) ∈ g.support := leadingMonomial_mem_support (ord := ord) g hg
  have hfcoeff : leadingCoefficient ord f ≠ 0 := (mem_support_iff f in[ord](f)).1 hfmem
  have hgcoeff : leadingCoefficient ord g ≠ 0 := (mem_support_iff g in[ord](g)).1 hgmem
  have hdiv : CMonomial.divides? in[ord](g) in[ord](f) := by
    by_cases h : CMonomial.divides? in[ord](g) in[ord](f)
    · exact h
    · simp [CMonomial.divide, h] at hm
  have hm' : in[ord](f) - in[ord](g) = m := by
    simpa [CMonomial.divide, hdiv] using hm
  have hdiv_all : ∀ i, in[ord](g) i ≤ in[ord](f) i :=
    (CMonomial.divides?_iff in[ord](g) in[ord](f)).1 hdiv
  have hmadd : m + in[ord](g) = in[ord](f) := by
    rw [← hm']
    ext i
    exact Nat.sub_add_cancel (hdiv_all i)
  let c : CMvPolynomial σ R :=
    CMvPolynomial.ofMonomial m (leadingCoefficient ord f / leadingCoefficient ord g)
  have hcoeffc : leadingCoefficient ord f / leadingCoefficient ord g ≠ 0 :=
    div_ne_zero hfcoeff hgcoeff
  have hc0 : c ≠ 0 := by
    intro hc
    have hcm : c m = 0 := by simp [hc]
    have hcm' : c m = leadingCoefficient ord f / leadingCoefficient ord g := by
      change (CMvPolynomial.ofMonomial m (leadingCoefficient ord f / leadingCoefficient ord g)) m =
        leadingCoefficient ord f / leadingCoefficient ord g
      simp [CMvPolynomial.ofMonomial]
    exact hcoeffc (hcm' ▸ hcm)
  have hlm_c : in[ord](c) = m := by
    simpa [c] using
      leadingMonomial_monomial (ord := ord) m
        (leadingCoefficient ord f / leadingCoefficient ord g) hcoeffc
  have hlm_cg : in[ord](c * g) = in[ord](f) := by
    calc
      in[ord](c * g) = in[ord](c) + in[ord](g) :=
        leadingMonomial_mul (ord := ord) c g hc0 hg
      _ = m + in[ord](g) := by simp [hlm_c]
      _ = in[ord](f) := hmadd
  have hlc_cg : leadingCoefficient ord (c * g) = leadingCoefficient ord f := by
    have hcoeff_top := coeff_mul_leadingMonomial_add (ord := ord) c g hc0 hg
    have hc_eval : c in[ord](c) = leadingCoefficient ord f / leadingCoefficient ord g := by
      rw [hlm_c]
      change (CMvPolynomial.ofMonomial m (leadingCoefficient ord f / leadingCoefficient ord g)) m =
        leadingCoefficient ord f / leadingCoefficient ord g
      simp [CMvPolynomial.ofMonomial]
    calc
      leadingCoefficient ord (c * g)
          = (c * g) in[ord](c * g) := rfl
      _ = (c * g) (in[ord](c) + in[ord](g)) := by
            simp [leadingMonomial_mul (ord := ord) c g hc0 hg]
      _ = c in[ord](c) * g in[ord](g) := hcoeff_top
      _ = (leadingCoefficient ord f / leadingCoefficient ord g) * leadingCoefficient ord g := by
        rw [hc_eval]
        rfl
      _ = leadingCoefficient ord f := by
            simpa [leadingCoefficient] using div_mul_cancel₀ (leadingCoefficient ord f) hgcoeff
  simpa [c] using
    terminationMeasure_sub_strict_of_same_leadingData
      (ord := ord) f (c * g) hf hlm_cg hlc_cg

set_option linter.unusedVariables false in
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
termination_by (ord.toSyn in[ord](f), f.support.card)
decreasing_by
  · simpa using mvDivide_decreases_some_branch (ord := ord) f g hf hg m hm
  · simpa using mvDivide_decreases_none_branch (ord := ord) f g hf hm

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
  have hr0 : r₂ - r₁ ≠ 0 := by
    haveI : NoZeroDivisors (CMvPolynomial σ R) := noZeroDivisors (ord := ord)
    have hmul0 : g * (q₁ - q₂) ≠ 0 := mul_ne_zero hg hq0
    intro hr
    apply hmul0
    rw [h, hr]
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
  classical
  let motive : CMvPolynomial σ R → Prop := fun x =>
    let (q, r) := mvDivide ord x g hg
    IsMvQuotientRemainder ord x g q r
  have hmain : ∀ x, motive x := by
    refine mvDivide.induct (ord := ord) (g := g) (hg := hg) (motive := motive) ?_ ?_ ?_
    · have h0 : mvDivide ord 0 g hg = (0, 0) := by
        simp [mvDivide.eq_def]
      simp [motive, h0, IsMvQuotientRemainder]
    · intro x hx0 m hm c q r hqr ih
      have ih' : IsMvQuotientRemainder ord (x - c * g) g q r := by
        simpa [motive, hqr]
          using ih
      rcases ih' with ⟨hdecomp, hrem⟩
      have hthis : IsMvQuotientRemainder ord x g (c + q) r := by
        refine ⟨?_, hrem⟩
        calc
          x = (x - c * g) + c * g := by ring
          _ = (g * q + r) + c * g := by simp [hdecomp]
          _ = g * (c + q) + r := by ring
      have hstep : mvDivide ord x g hg = (c + q, r) := by
        have hqr' :
            mvDivide ord
              (x
                - CMvPolynomial.ofMonomial m
                    (leadingCoefficient ord x / leadingCoefficient ord g) * g)
              g hg = (q, r) := by
          simpa [c] using hqr
        have hstep' :
            mvDivide ord x g hg =
              (CMvPolynomial.ofMonomial m
                  (leadingCoefficient ord x / leadingCoefficient ord g)
                + q, r) := by
          by_cases hx : x = 0
          · exact (hx0 hx).elim
          · rw [mvDivide.eq_def]
            rw [hm]
            simp [hx, hqr']
        simpa [c] using hstep'
      simpa [motive, hstep, c] using hthis
    · intro x hx0 hm lt_f q r hqr ih
      have ih' : IsMvQuotientRemainder ord (x - lt_f) g q r := by
        simpa [motive, hqr]
          using ih
      rcases ih' with ⟨hdecomp, hrem⟩
      have hxmem : in[ord](x) ∈ x.support := leadingMonomial_mem_support (ord := ord) x hx0
      have hxc : leadingCoefficient ord x ≠ 0 := (mem_support_iff x in[ord](x)).1 hxmem
      have hltf_eq : lt_f = leadingTerm ord x := rfl
      have hndiv : ¬ CMonomial.divides? in[ord](g) in[ord](x) := by
        intro hdiv
        have hsome : CMonomial.divide in[ord](x) in[ord](g) = some (in[ord](x) - in[ord](g)) :=
          CMonomial.divide_eq_some_of_divides? hdiv
        have : (none : Option (CMonomial σ)) = some (in[ord](x) - in[ord](g)) := hm.symm.trans hsome
        cases this
      have hthis : IsMvQuotientRemainder ord x g q (r + lt_f) := by
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
      have hstep : mvDivide ord x g hg = (q, r + lt_f) := by
        have hqr' : mvDivide ord (x - leadingTerm ord x) g hg = (q, r) := by
          simpa [hltf_eq] using hqr
        have hstep' : mvDivide ord x g hg = (q, r + leadingTerm ord x) := by
          by_cases hx : x = 0
          · exact (hx0 hx).elim
          · rw [mvDivide.eq_def]
            rw [hm]
            simp [hx, hqr']
        simpa [hltf_eq] using hstep'
      simpa [motive, hstep] using hthis
  simpa [motive] using hmain f

end CMvPolynomial
