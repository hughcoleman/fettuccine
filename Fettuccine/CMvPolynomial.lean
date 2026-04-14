import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.DFinsupp.Order

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

-- There is a natural preorder on `CMonomial σ` given by the pointwise order on
-- the underlying functions. Every monomial order must inherit this order.
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

/-- The degree of a monomial is additive. -/
lemma degree_add (m₁ m₂ : CMonomial σ) : degree (m₁ + m₂) = degree m₁ + degree m₂ := by
  sorry

/-- A monomial is squarefree if no variables appear with exponent greater than 1. -/
def isSquarefree (m : CMonomial σ) : Prop :=
  ∀ x ∈ m.support, m x = 1 -- (zero is implicitly excluded from the support)

end CMonomial

/-! ## CMvPolynomial -/

open DirectSum

abbrev CMvPolynomial (σ : Type*) [DecidableEq σ] (R : Type*) [CommSemiring R] :=
  ⨁ _ : CMonomial σ, R

namespace CMvPolynomial

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [CommSemiring R]

@[simp] lemma mem_support_iff [DecidableEq R] (p : CMvPolynomial σ R) (m : CMonomial σ) :
    m ∈ p.support ↔ p m ≠ 0 :=
  sorry

/-- The variable `xᵢ` as a polynomial. -/
def X (i : σ) : CMvPolynomial σ R :=
  DirectSum.of (fun _ => R) (CMonomial.X i) 1

/-- The constant polynomial with value `a`. -/
def C (a : R) : CMvPolynomial σ R :=
  DirectSum.of (fun _ => R) 0 a

/-- The polynomial with a single term `a m`. -/
def ofMonomial (m : CMonomial σ) (a : R) : CMvPolynomial σ R :=
  DirectSum.of (fun _ => R) m a

lemma support_ofMonomial [DecidableEq R] (m : CMonomial σ) (c : R) (hc : c ≠ 0) :
    (ofMonomial m c).support = {m} := by
  sorry

end CMvPolynomial
