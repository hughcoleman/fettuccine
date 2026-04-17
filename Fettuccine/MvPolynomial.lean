import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.DFinsupp.Order
import Mathlib.Data.Finset.NAry

/-!
# Multivariate Polynomials

This file defines the types `Monomial σ` and `MvPolynomial σ R`.

## Definitions

* `Monomial σ` : the type of monomials with variables `σ`.
* `Monomial.X i` : the monomial `xᵢ` (variable `i` with exponent 1).
* `MvPolynomial σ R` : the type of multivariate polynomials with variables `σ`
  and coefficients `R`.
* `MvPolynomial.X i` : the polynomial `xᵢ`.
* `MvPolynomial.C a` : the constant polynomial with value `a`.
-/

/-- A computable monomial in variables `σ` is a finitely-supported function
    `σ → ℕ` recording the exponent of each variable. -/
abbrev Monomial (σ : Type*) [DecidableEq σ] :=
  Π₀ _ : σ, ℕ

namespace Monomial

variable {σ : Type*} [DecidableEq σ]

-- There is a natural preorder on `Monomial σ` given by the pointwise order on the underlying
-- functions. Every monomial order must inherit this order, so we define it here.
instance [DecidableEq σ] : Preorder (Monomial σ) where
  le a b := a.toFun ≤ b.toFun
  le_refl _ := by
    simp_all only [le_refl]
  le_trans _ _ _ hab hbc :=
    le_trans hab hbc

/-- The monomial `xᵢ` (variable `i` with exponent 1). -/
def X (i : σ) : Monomial σ := DFinsupp.single i 1

@[simp] lemma mem_support_iff (m : Monomial σ) (x : σ) : x ∈ m.support ↔ m x ≠ 0 :=
  DFinsupp.mem_support_iff

@[simp] lemma support_add_eq (m₁ m₂ : Monomial σ) :
    (m₁ + m₂).support = m₁.support ∪ m₂.support := by
  ext i; simp; omega

/-- The degree of a monomial is the sum of its exponents. -/
def degree (m : Monomial σ) : ℕ := m.support.sum (m ·)

lemma sum_union_support_eq (m : Monomial σ) (t : Finset σ) :
    (m.support ∪ t).sum (fun i => m i) = m.support.sum (fun i => m i) := by
  classical
    refine (Finset.sum_subset (Finset.subset_union_left (s₁ := m.support) (s₂ := t)) ?_).symm
    intro i _ hi; simpa using (DFinsupp.notMem_support_iff).mp hi

/-- The degree of a monomial is additive. -/
lemma degree_add (m₁ m₂ : Monomial σ) : degree (m₁ + m₂) = degree m₁ + degree m₂ := by
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
            simp [Monomial.support_add_eq, DFinsupp.add_apply]
    _ = (m₁.support ∪ m₂.support).sum (fun i => m₁ i) +
        (m₁.support ∪ m₂.support).sum (fun i => m₂ i) := by
            simp [Finset.sum_add_distrib]
    _ = m₁.support.sum (fun i => m₁ i) + m₂.support.sum (fun i => m₂ i) := by
            simp [hsum₁, hsum₂]

/-- A monomial is squarefree if no variables appear with exponent greater than 1. -/
def isSquarefree (m : Monomial σ) : Prop :=
  ∀ x ∈ m.support, m x = 1 -- (zero is implicitly excluded from the support)

/-- Least common multiple of monomials, computed pointwise. -/
def lcm (m₁ m₂ : Monomial σ) : Monomial σ :=
  DFinsupp.zipWith (fun _ a b => max a b) (fun _ => by simp) m₁ m₂

end Monomial

open DirectSum

abbrev MvPolynomial (σ : Type*) [DecidableEq σ] (R : Type*) [CommSemiring R] :=
  ⨁ _ : Monomial σ, R

namespace MvPolynomial

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [CommSemiring R]

/-- The variable `xᵢ` as a polynomial. -/
def X (i : σ) : MvPolynomial σ R :=
  DirectSum.of (fun _ => R) (Monomial.X i) 1

/-- The constant polynomial with value `a`. -/
def C (a : R) : MvPolynomial σ R :=
  DirectSum.of (fun _ => R) 0 a

/-- The polynomial with a single term `a m`. -/
def ofMonomial (m : Monomial σ) (a : R) : MvPolynomial σ R :=
  DirectSum.of (fun _ => R) m a

/-- The coefficient of monomial `m` in polynomial `f`. -/
@[simp] def coefficientOf (f : MvPolynomial σ R) (m : Monomial σ) : R :=
  f m

variable [DecidableEq R]

/-- The support of a monomial polynomial is singleton. -/
lemma support_ofMonomial (m : Monomial σ) (a : R) (ha : a ≠ 0) :
    (ofMonomial m a).support = {m} := by
  simpa [ofMonomial] using
    (DirectSum.support_of (β := fun _ : Monomial σ => R) m a ha)

-- Equivalent characterizations of non-zero polynomials in terms of the support.
@[simp] lemma support_nonempty_iff (f : MvPolynomial σ R) :
    f.support.Nonempty ↔ f ≠ 0 := by
  have h₁ : f.support.Nonempty ↔ f.support ≠ ∅ := by
    simp only [Finset.nonempty_iff_ne_empty]
  have h₂ : f.support ≠ ∅ ↔ f ≠ 0 := by
    simp [DFinsupp.support_eq_empty]; rfl
  exact Iff.trans h₁ h₂

/-- A monomial is an element of the support if and only if its coefficient is non-zero. -/
@[simp] lemma mem_support_iff (f : MvPolynomial σ R) (m : Monomial σ) :
    m ∈ f.support ↔ f m ≠ 0 := by
  simp only [DFinsupp.mem_support_toFun, ne_eq]

/-- The support of a sum of two polynomials is contained in the union of the supports of the
    summands. -/
lemma support_add_subset (f g : MvPolynomial σ R) :
    (f + g).support ⊆ f.support ∪ g.support := by
  exact DFinsupp.support_add

/-- The support of a product two of polynomials is contained in the "Cartesian" product of the
    supports of its factors. -/
lemma support_mul_subset (f g : MvPolynomial σ R) :
    (f * g).support ⊆ Finset.image₂ (· + ·) f.support g.support := by
  classical
  -- We can express the product `f * g` as a sum over all pairs of monomials in the supports of `f`
  -- and `g`, where the coefficient of each monomial is given by the product of the corresponding
  -- coefficients in `f` and `g`.
  let termOf : Monomial σ × Monomial σ → MvPolynomial σ R
  | ⟨i, j⟩ => MvPolynomial.ofMonomial (i + j) (f.coefficientOf i * g.coefficientOf j)
  have mul_eq : f * g = ∑ ij ∈ f.support ×ˢ g.support, termOf ij := by
    simpa [termOf] using (DirectSum.mul_eq_sum_support_ghas_mul _ f g)
  -- To prove that the support of the product is contained in the union of the supports, we prove
  -- the stronger claim that this holds for any finite set of monomials. (This can be done by
  -- induction on the size of the finite set.)
  have support :
      (f * g).support ⊆ (f.support ×ˢ g.support).biUnion (fun ij => (termOf ij).support) := by
    suffices h' : ∀ s : Finset (Monomial σ × Monomial σ),
        (∑ ij ∈ s, termOf ij).support ⊆ s.biUnion (fun ij => (termOf ij).support) by
      simpa [mul_eq] using h' (f.support ×ˢ g.support)
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp [DirectSum.support_zero]
    · intro a s ha hs
      have h₁ :
          (termOf a + ∑ ij ∈ s, termOf ij).support
            ⊆ (termOf a).support ∪ (∑ ij ∈ s, termOf ij).support := by
        simpa using (DFinsupp.support_add (g₁ := termOf a) (g₂ := ∑ ij ∈ s, termOf ij))
      have h₂ :
          (termOf a).support ∪ (∑ ij ∈ s, termOf ij).support
            ⊆ (termOf a).support ∪ s.biUnion (fun ij => (termOf ij).support) :=
        Finset.union_subset_union (subset_refl _) hs
      simpa [Finset.sum_insert, ha, Finset.biUnion_insert] using (h₁.trans h₂)
  -- Pass to the remaining containment.
  refine support.trans ?_
  refine (Finset.biUnion_subset).mpr ?_
  intro ⟨i, j⟩ h
  -- Replace `h` with an equivalent formulation in terms of membership in `f` and `g`.
  replace h : i ∈ f.support ∧ j ∈ g.support := by
    simpa [Finset.mem_product] using h
  -- The term of `⟨i, j⟩` has support contained in `{i + j}`.
  have ij_support : (termOf ⟨i, j⟩).support ⊆ {i + j} := by
    simpa [termOf] using
      (DirectSum.support_of_subset (β := fun _ : Monomial σ => R)
        (i := i + j) (b := (f.coefficientOf i) * (g.coefficientOf j)))
  exact ij_support.trans ((Finset.singleton_subset_iff).mpr (Finset.mem_image₂_of_mem h.1 h.2))

/-- If the coefficient ring is nontrivial, then so is the polynomial ring. -/
instance [Nontrivial R] : Nontrivial (MvPolynomial σ R) where
  exists_pair_ne := by
    -- Lift a pair of distinct elements of `R` to a pair of constant polynomials.
    obtain ⟨a, b, h⟩ := exists_pair_ne R
    refine ⟨MvPolynomial.C a, MvPolynomial.C b, ?_⟩
    -- These must be distinct because they are distinct when evaluated at, among other places, zero.
    intro hC
    exact h <| by
      simpa [MvPolynomial.C, MvPolynomial.coefficientOf] using
        congrArg (fun p : MvPolynomial σ R => p.coefficientOf 0) hC

end MvPolynomial
