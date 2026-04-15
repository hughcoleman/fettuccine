import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.DFinsupp.Order
import Mathlib.Data.Finset.NAry

/-!
# Computable Multivariate Polynomials

This file defines the types `CMonomial σ` and `CMvPolynomial σ R`, which are
computable realizations of `σ →₀ ℕ` and `MvPolynomial σ R` respectively.

## Definitions

* `CMonomial σ` : the type of monomials with variables `σ`.
* `CMonomial.X i` : the monomial `xᵢ` (variable `i` with exponent 1).
* `CMvPolynomial σ R` : the type of multivariate polynomials with variables `σ`
  and coefficients `R`.
* `CMvPolynomial.X i` : the polynomial `xᵢ`.
* `CMvPolynomial.C a` : the constant polynomial with value `a`.
-/

/-! ## CMonomial -/

/-- A computable monomial in variables `σ` is a finitely-supported function
    `σ → ℕ` recording the exponent of each variable. -/
abbrev CMonomial (σ : Type*) [DecidableEq σ] :=
  Π₀ _ : σ, ℕ

namespace CMonomial

variable {σ : Type*} [DecidableEq σ]

-- There is a natural preorder on `CMonomial σ` given by the pointwise order on the underlying
-- functions. Every monomial order must inherit this order, so we define it here.
instance [DecidableEq σ] : Preorder (CMonomial σ) where
  le a b := a.toFun ≤ b.toFun
  le_refl _ := by
    simp_all only [le_refl]
  le_trans _ _ _ hab hbc :=
    le_trans hab hbc

/-- The monomial `xᵢ` (variable `i` with exponent 1). -/
def X (i : σ) : CMonomial σ := DFinsupp.single i 1

@[simp] lemma mem_support_iff (m : CMonomial σ) (x : σ) : x ∈ m.support ↔ m x ≠ 0 :=
  DFinsupp.mem_support_iff

@[simp] lemma support_add_eq (m₁ m₂ : CMonomial σ) :
    (m₁ + m₂).support = m₁.support ∪ m₂.support := by
  ext i; simp; omega

/-- The degree of a monomial is the sum of its exponents. -/
def degree (m : CMonomial σ) : ℕ := m.support.sum (m ·)

lemma sum_union_support_eq (m : CMonomial σ) (t : Finset σ) :
    (m.support ∪ t).sum (fun i => m i) = m.support.sum (fun i => m i) := by
  classical
    refine (Finset.sum_subset (Finset.subset_union_left (s₁ := m.support) (s₂ := t)) ?_).symm
    intro i _ hi; simpa using (DFinsupp.notMem_support_iff).mp hi

/-- The degree of a monomial is additive. -/
lemma degree_add (m₁ m₂ : CMonomial σ) : degree (m₁ + m₂) = degree m₁ + degree m₂ := by
  classical
  -- Expand the degree as a sum over the union of supports.
  unfold degree
  have hsum₁ :
      (m₁.support ∪ m₂.support).sum (fun i => m₁ i) = m₁.support.sum (fun i => m₁ i) := by
    exact sum_union_support_eq (m := m₁) (t := m₂.support)
  have hsum₂ :
      (m₁.support ∪ m₂.support).sum (fun i => m₂ i) = m₂.support.sum (fun i => m₂ i) := by
    simpa [Finset.union_comm] using sum_union_support_eq (m := m₂) (t := m₁.support)
  calc
    (m₁ + m₂).support.sum (fun i => (m₁ + m₂) i)
    _ = (m₁.support ∪ m₂.support).sum (fun i => m₁ i + m₂ i) := by
            simp [CMonomial.support_add_eq, DFinsupp.add_apply]
    _ = (m₁.support ∪ m₂.support).sum (fun i => m₁ i) +
        (m₁.support ∪ m₂.support).sum (fun i => m₂ i) := by
            simp [Finset.sum_add_distrib]
    _ = m₁.support.sum (fun i => m₁ i) + m₂.support.sum (fun i => m₂ i) := by
            simp [hsum₁, hsum₂]

/-- A monomial is squarefree if no variables appear with exponent greater than 1. -/
def isSquarefree (m : CMonomial σ) : Prop :=
  ∀ x ∈ m.support, m x = 1 -- (zero is implicitly excluded from the support)

/-- Least common multiple of monomials, computed pointwise. -/
def lcm (m₁ m₂ : CMonomial σ) : CMonomial σ :=
  DFinsupp.zipWith (fun _ a b => max a b) (fun _ => by simp) m₁ m₂

end CMonomial

/-! ## CMvPolynomial -/

open DirectSum

abbrev CMvPolynomial (σ : Type*) [DecidableEq σ] (R : Type*) [CommSemiring R] :=
  ⨁ _ : CMonomial σ, R

namespace CMvPolynomial

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [CommSemiring R]

/-- The variable `xᵢ` as a polynomial. -/
def X (i : σ) : CMvPolynomial σ R :=
  DirectSum.of (fun _ => R) (CMonomial.X i) 1

/-- The constant polynomial with value `a`. -/
def C (a : R) : CMvPolynomial σ R :=
  DirectSum.of (fun _ => R) 0 a

/-- The polynomial with a single term `a m`. -/
def ofMonomial (m : CMonomial σ) (a : R) : CMvPolynomial σ R :=
  DirectSum.of (fun _ => R) m a

lemma support_ofMonomial [DecidableEq R] (m : CMonomial σ) (a : R) (ha : a ≠ 0) :
    (ofMonomial m a).support = {m} := by
  simpa [ofMonomial] using
    (DirectSum.support_of (β := fun _ : CMonomial σ => R) m a ha)

@[simp] lemma support_nonempty_iff [DecidableEq R] (f : CMvPolynomial σ R) :
    f.support.Nonempty ↔ f ≠ 0 := by
  have h₁ : f.support.Nonempty ↔ f.support ≠ ∅ := by
    simp only [Finset.nonempty_iff_ne_empty]
  have h₂ : f.support ≠ ∅ ↔ f ≠ 0 := by
    simp [DFinsupp.support_eq_empty]; rfl
  exact Iff.trans h₁ h₂

@[simp] lemma mem_support_iff [DecidableEq R] (f : CMvPolynomial σ R) (m : CMonomial σ) :
    m ∈ f.support ↔ f m ≠ 0 := by
  simp only [DFinsupp.mem_support_toFun, ne_eq]

/-- The support of a sum is contained in the union of the supports of its summands. -/
lemma support_add_subset [DecidableEq R] (f g : CMvPolynomial σ R) :
    (f + g).support ⊆ f.support ∪ g.support := by
  exact DFinsupp.support_add

/-- The support of a product is contained in the product of the supports of its factors. -/
lemma support_mul_subset [DecidableEq R] (f g : CMvPolynomial σ R) :
    (f * g).support ⊆ Finset.image₂ (· + ·) f.support g.support := by
  -- [TO-REVIEW]
  classical
  -- Expand the product as a sum over pairs of support monomials.
  let mulTerm : CMonomial σ × CMonomial σ → CMvPolynomial σ R := fun ij =>
    DirectSum.of (fun _ : CMonomial σ => R) (ij.1 + ij.2) (f ij.1 * g ij.2)
  have mul_eq : f * g =
      ∑ ij ∈ f.support ×ˢ g.support, mulTerm ij := by
    simpa [mulTerm] using
      (DirectSum.mul_eq_sum_support_ghas_mul (A := fun _ : CMonomial σ => R) (a := f) (a' := g))
  have support_sum_subset :
      ∀ s : Finset (CMonomial σ × CMonomial σ),
        (∑ ij ∈ s, mulTerm ij).support ⊆ s.biUnion (fun ij => (mulTerm ij).support) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp [DirectSum.support_zero]
    · intro a s ha hs
      have hsubset :
          (mulTerm a + ∑ ij ∈ s, mulTerm ij).support
            ⊆ (mulTerm a).support ∪ (∑ ij ∈ s, mulTerm ij).support := by
        simpa using (DFinsupp.support_add (g₁ := mulTerm a) (g₂ := ∑ ij ∈ s, mulTerm ij))
      have hsubset' :
          (mulTerm a).support ∪ (∑ ij ∈ s, mulTerm ij).support
            ⊆ (mulTerm a).support ∪ s.biUnion (fun ij => (mulTerm ij).support) :=
        Finset.union_subset_union (subset_refl _) hs
      simpa [Finset.sum_insert, ha, Finset.biUnion_insert] using (hsubset.trans hsubset')
  -- The support of a sum is contained in the union of the supports of its terms.
  have support_subset : (f * g).support ⊆
      (f.support ×ˢ g.support).biUnion (fun ij => (mulTerm ij).support) := by
    simpa [mul_eq] using
      (support_sum_subset (f.support ×ˢ g.support))
  refine support_subset.trans ?_
  refine (Finset.biUnion_subset).2 ?_
  intro ij hij
  -- Each term is supported only on the sum of its indices.
  have term_support : (mulTerm ij).support ⊆ {ij.1 + ij.2} := by
    simpa [mulTerm] using
      (DirectSum.support_of_subset (β := fun _ : CMonomial σ => R)
        (i := ij.1 + ij.2) (b := (f ij.1) * (g ij.2)))
  have hij' : ij.1 ∈ f.support ∧ ij.2 ∈ g.support := by
    simpa [Finset.mem_product] using hij
  have sum_mem : ij.1 + ij.2 ∈ Finset.image₂ (· + ·) f.support g.support :=
    Finset.mem_image₂_of_mem hij'.1 hij'.2
  exact term_support.trans ((Finset.singleton_subset_iff).2 sum_mem)

/-- If the coefficient ring is nontrivial, then so is the polynomial ring. -/
instance [Nontrivial R] : Nontrivial (CMvPolynomial σ R) where
  exists_pair_ne := by
    -- [TO-REVIEW]
    obtain ⟨a, b, hne⟩ := exists_pair_ne R
    refine ⟨CMvPolynomial.C a, CMvPolynomial.C b, ?_⟩
    intro hC
    apply hne
    exact congrArg (fun p : CMvPolynomial σ R => p 0) hC

end CMvPolynomial
