import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.DFinsupp.Lex
import Mathlib.Data.Finset.Sort

/-!
# Computable Multivariate Polynomials

This file defines the types `CMonomial σ` and `CMvPolynomial σ R`, which are
computable analogues of `σ →₀ ℕ` and `MvPolynomial σ R` respectively.

## Definitions

* `CMonomial σ` : the type of monomials with variables `σ`.
* `CMonomial.X i` : the monomial `xᵢ` (variable `i` with exponent 1).
* `CMvPolynomial σ R` : the type of multivariate polynomials with variables `σ`
  and coefficients `R`.
* `CMvPolynomial.X i` : the polynomial `xᵢ`.
* `CMvPolynomial.C a` : the constant polynomial with value `a`.
-/

/-- An instance of `Repr` for `Fin n`, displaying as x₀, x₁, etc. -/
instance Fin.fallbackRepr {n : ℕ} : Repr (Fin n) where
  reprPrec i _ := "x" ++ String.map digits (toString i.val)
where
  digits : Char → Char
    | '0' => '₀' | '1' => '₁' | '2' => '₂' | '3' => '₃' | '4' => '₄'
    | '5' => '₅' | '6' => '₆' | '7' => '₇' | '8' => '₈' | '9' => '₉'
    | c   => c

/-! ## CMonomial -/

/-- A computable monomial in variables `σ` is a finitely-supported function
    `σ → ℕ` recording the exponent of each variable. -/
-- This is defined as an opaque structure to avoid conflicts with instances
-- provided by `DFinsupp` instances.
structure CMonomial (σ : Type*) [DecidableEq σ] where
  /-- The underlying finitely-supported exponent function. -/
  toFun : Π₀ _ : σ, ℕ

attribute [coe] CMonomial.toFun

namespace CMonomial

variable {σ : Type*} [DecidableEq σ]

/-- Equality of monomials is decidable. -/
instance : DecidableEq (CMonomial σ) :=
  fun m₁ m₂ => decidable_of_iff (m₁.toFun = m₂.toFun)
    ⟨fun h => by cases m₁; cases m₂; exact congrArg _ h, fun h => by cases h; rfl⟩

/-- Since the underlying representation is a function, a monomial is `FunLike`. -/
instance : FunLike (CMonomial σ) σ ℕ where
  coe p := p.toFun
  coe_injective' p₁ p₂ h := by cases p₁; cases p₂; simp_all

/-- Construct a `CMonomial` from a `DFinsupp`. -/
def ofFun (f : Π₀ _ : σ, ℕ) : CMonomial σ := ⟨f⟩

/-- `CMonomial σ` is equivalent to `Π₀ _ : σ, ℕ`. -/
def equiv : CMonomial σ ≃ (Π₀ _ : σ, ℕ) where
  toFun  := toFun
  invFun := ofFun

@[ext]
lemma ext {m₁ m₂ : CMonomial σ} (h : ∀ i, m₁ i = m₂ i) : m₁ = m₂ :=
  DFunLike.ext _ _ h

-- `CMonomial σ` can be endowed with the structure of an additive commutative
-- monoid, lifted from the corresponding structure on `Π₀ _ : σ, ℕ`.
instance : AddCommMonoid (CMonomial σ) :=
  equiv.addCommMonoid

-- The equivalnce is, by construction, additive.
@[simp] lemma toFun_add (m₁ m₂ : CMonomial σ) : (m₁ + m₂).toFun = m₁.toFun + m₂.toFun :=
  rfl

@[simp] lemma coe_add (m₁ m₂ : CMonomial σ) (x : σ) : (m₁ + m₂) x = m₁ x + m₂ x :=
  rfl

/-- The monomial `xᵢ` (variable `i` with exponent 1). -/
def X (i : σ) : CMonomial σ := ⟨DFinsupp.single i 1⟩

/-- The support of a monomial are its variables with non-zero exponent. -/
def support (m : CMonomial σ) : Finset σ := m.toFun.support

@[simp] lemma mem_support_iff (m : CMonomial σ) (x : σ) : x ∈ m.support ↔ m x ≠ 0 :=
  DFinsupp.mem_support_iff

@[simp] lemma support_add_eq (m₁ m₂ : CMonomial σ) :
    (m₁ + m₂).support = m₁.support ∪ m₂.support := by
  ext i; simp; omega

/-- The degree of a monomial is the sum of its exponents. -/
def degree (m : CMonomial σ) : ℕ := m.support.sum (m ·)

/-- The degree of a monomial is additive. -/
lemma degree_add (m₁ m₂ : CMonomial σ) : degree (m₁ + m₂) = degree m₁ + degree m₂ := by
  simp only [degree, support_add_eq, coe_add]
  rw [Finset.sum_add_distrib]; congr 1
  · refine Finset.sum_union_eq_left ?_
    intro a _ ha; simp_all
  · refine Finset.sum_union_eq_right ?_
    intro a _ ha; simp_all

/-- Display a monomial as a product of variables with exponents. -/
instance [LinearOrder σ] [Repr σ] : Repr (CMonomial σ) where
  reprPrec m _ :=
    let terms := m.support.sort (· ≤ ·)
      |>.filterMap fun i =>
        match m i with
        | 0 => none
        | 1 => some f!"{reprPrec i 0}"
        | e => some f!"{reprPrec i 0}^{e}"
    if terms.isEmpty then "1"
    else
      Std.Format.joinSep terms ""

end CMonomial

/-! ## CMvPolynomial -/

open DirectSum

/-- A computable multivariate polynomial over the coefficient ring `R` in
    variables `σ` is a finitely-supported function from `CMonomial σ` to `R`. -/
structure CMvPolynomial (σ : Type*) [DecidableEq σ] (R : Type*) [CommSemiring R] where
  toFun : ⨁ _ : CMonomial σ, R

attribute [coe] CMvPolynomial.toFun

namespace CMvPolynomial

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [CommSemiring R]

/-- Equality of multivariate polynomials is decidable. -/
instance [DecidableEq R] : DecidableEq (CMvPolynomial σ R) :=
  fun p q => decidable_of_iff (p.toFun = q.toFun)
    ⟨fun h => by cases p; cases q; simp_all, fun h => by cases h; rfl⟩

/-- Since the underlying representation is a function, a multivariate
    polynomial is `FunLike`. -/
instance : FunLike (CMvPolynomial σ R) (CMonomial σ) R where
  coe p := p.toFun
  coe_injective' p₁ p₂ h := by cases p₁; cases p₂; simp_all

/-- Construct a `CMvPolynomial` from a `DirectSum`. -/
def ofFun (f : ⨁ _ : CMonomial σ, R) : CMvPolynomial σ R := ⟨f⟩

/-- `CMvPolynomial σ R` is equivalent to `⨁ _ : CMonomial σ, R`. -/
def equiv : CMvPolynomial σ R ≃ (⨁ _ : CMonomial σ, R) where
  toFun  := toFun
  invFun := ofFun

-- `CMvPolynomial σ` can be endowed with the structure of a commutative
-- semiring, lifted from the corresponding structure on `⨁ _ : CMonomial σ, R`.
instance : CommSemiring (CMvPolynomial σ R) :=
  equiv.commSemiring

/-- The support of a monomial are its terms with non-zero coefficient. -/
def support [DecidableEq R] (p : CMvPolynomial σ R) : Finset (CMonomial σ) :=
  p.toFun.support

@[simp] lemma mem_support_iff [DecidableEq R] (p : CMvPolynomial σ R) (m : CMonomial σ) :
    m ∈ p.support ↔ p m ≠ 0 :=
  DFinsupp.mem_support_iff

/-- The variable `xᵢ` as a polynomial. -/
def X (i : σ) : CMvPolynomial σ R :=
  ⟨DirectSum.of (fun _ => R) (CMonomial.X i) 1⟩

/-- The constant polynomial with value `a`. -/
def C (a : R) : CMvPolynomial σ R :=
  ⟨DirectSum.of (fun _ => R) 0 a⟩

/-- Display a polynomial as a sum of terms. -/
-- THIS IS UGLY. We should implement this in terms of a CMonomialOrder.
instance [DecidableEq R] [LinearOrder σ] [Repr σ] [Repr R] :
    Repr (CMvPolynomial σ R) where
  reprPrec f _ :=
    -- We'll display the monomials in the lexicographic order, for now.
    haveI : LinearOrder (CMonomial σ) := LinearOrder.lift'
      (fun m => toLex m.toFun)
      (fun m₁ m₂ h => by cases m₁; cases m₂; simp_all)
    let terms := f.toFun.support.sort (· ≤ ·)
      |>.filterMap fun m =>
        let coeff := f m
        if      coeff == 0 then none
        else if coeff == 1 then some (reprPrec m 0)
        else                    some f!"{reprPrec coeff 0}{reprPrec m 0}"
    if terms.isEmpty then "0"
    else
      Std.Format.joinSep terms " + "

end CMvPolynomial

#min_imports
