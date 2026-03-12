import Aesop
import Mathlib.Data.Finsupp.Basic
import Mathlib.Order.Basic

/-!
# Multivariate polynomials

This file defines computable types for operating on multivariate polynomials
over commutative rings.

## Definitions

- `MvPolynomial σ R`: the type of polynomials with variables of type `σ` and
  variables in a commutative semiring `R`.
-/

/-- A monomial with variables `σ`. -/
-- For the time being, we will store monomials with the variables arranged in
-- **strictly decreasing** order and without redundancy, and will carefully
-- maintain these invariants.
abbrev CMonomial (σ : Type*) [LinearOrder σ] := List (σ × ℕ)

namespace CMonomial

variable {σ : Type*} [LinearOrder σ]

/-- The one monomial. -/
def one : CMonomial σ := []

/-- Compute the product of two monomials. -/
def mul (a b : CMonomial σ) : CMonomial σ :=
  match a, b with
  | _, [] => a
  | [], _ => b
  | (x₁, n₁) :: as, (x₂, n₂) :: bs =>
    match compare x₁ x₂ with
    | -- Since n₁ and n₂ are both positive, it follows that n₁ + n₂ ≥ 2, and so
      -- this does not introduce redundancy.
      Ordering.eq => (x₁, n₁ + n₂) :: mul as bs
    | Ordering.gt => (x₁, n₁) :: mul as ((x₂, n₂) :: bs)
    | Ordering.lt => (x₂, n₂) :: mul ((x₁, n₁) :: as) bs

/-- Compute the lowest common multiple of two monomials. -/
def lcm (a b : CMonomial σ) : CMonomial σ :=
  match a, b with
  | _, [] => a
  | [], _ => b
  | (x₁, n₁) :: as, (x₂, n₂) :: bs =>
    match compare x₁ x₂ with
    | Ordering.eq => (x₁, max n₁ n₂) :: lcm as bs
    | Ordering.gt => (x₁, n₁) :: lcm as ((x₂, n₂) :: bs)
    | Ordering.lt => (x₂, n₂) :: lcm ((x₁, n₁) :: as) bs

end CMonomial

/-- A multivariate polynomial with variables `σ` and coefficients in `R`. -/
abbrev CMvPolynomial (σ : Type*) (R : Type*) [LinearOrder σ] [CommSemiring R] :=
  List ((CMonomial σ) × R)

namespace CMvPolynomial

variable {σ : Type*} [LinearOrder σ]
variable {R : Type*} [CommSemiring R]

/-- The zero polynomial. -/
def zero : CMvPolynomial σ R := []

/-- The one polynomial. -/
def one : CMvPolynomial σ R := [(CMonomial.one, 1)]

/-- Compute the sum of two polynomials. -/
def add (f g : CMvPolynomial σ R) : CMvPolynomial σ R :=
  sorry

/-- Negate a polynomial. -/
def neg (f : CMvPolynomial σ R) : CMvPolynomial σ R :=
  sorry

/-- Compute the product of two polynomials. -/
def mul (f g : CMvPolynomial σ R) : CMvPolynomial σ R :=
  sorry

end CMvPolynomial
