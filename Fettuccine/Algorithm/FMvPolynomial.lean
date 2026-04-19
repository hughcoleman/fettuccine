import Mathlib.Algebra.Group.Basic

/-!
# Fast Multivariate Polynomials

This file defines the types `FMonomial n` and `FMvPolynomial n R`, which are primitive
representations of monomials (`CMonomial σ`) and multivariate polynomials (`CMvPolynomial σ R`).

## Definitions

- `FMonomial n` : the type of monomials on `n` variables; `m[i]` is the exponent of variable `i`.
- `FMonomial.X i` : the monomial `xᵢ` (variable `i` with exponent 1).
- `FMvPolynomial n R` : normalized array of `(monomial, coefficient)` pairs.
- `FMvPolynomial.X i` : the polynomial `xᵢ`.
- `FMvPolynomial.C a` : the constant polynomial with value `a`.
-/

/-- A monomial on `n` variables is represented as an array of exponents alongside a proof that it is
    of the expected length. -/
structure FMonomial (n : ℕ) where
  data : Array ℕ
  hsize : data.size = n
deriving DecidableEq

namespace FMonomial

variable {n : ℕ}

@[simp] theorem size_data (m : FMonomial n) : m.data.size = n := m.hsize

/-- Convert a monomial to its exponent list. -/
def toList (m : FMonomial n) : List ℕ := m.data.toList

/-- The zero monomial on `n` variables. -/
def zero (n : ℕ) : FMonomial n where
  data := Array.replicate n 0
  hsize := by simp

/-- The monomial `xᵢ`: exponent 1 at position `i`, 0 elsewhere. -/
def X (i : Fin n) : FMonomial n where
  data := Array.ofFn (fun j : Fin n => if j = i then 1 else 0)
  hsize := by simp

/-- The degree of a monomial. -/
def degree (m : FMonomial n) : ℕ := m.data.foldl (· + ·) 0

/-- The product of two monomials (component-wise addition of exponents). -/
def add (m₁ m₂ : FMonomial n) : FMonomial n where
  data := Array.zipWith (· + ·) m₁.data m₂.data
  hsize := by simp [m₁.hsize, m₂.hsize]

/-- The lowest common multiple of two monomials (component-wise maximum of exponents). -/
def lcm (m₁ m₂ : FMonomial n) : FMonomial n where
  data := Array.zipWith max m₁.data m₂.data
  hsize := by simp [m₁.hsize, m₂.hsize]

end FMonomial

/-- A multivariate polynomial, represented as an array of monomial-coefficient pairs, stored sorted
    according to a (fixed, implicit) monomial order. -/
abbrev FMvPolynomial (n : ℕ) (R : Type*) := Array (FMonomial n × R)

namespace FMvPolynomial

variable {n : ℕ}
variable {R : Type*}

/-- The zero polynomial. -/
def zero : FMvPolynomial n R := #[]

/-- The polynomial `xᵢ`. -/
def X [One R] (i : Fin n) : FMvPolynomial n R := #[(FMonomial.X i, 1)]

/-- The constant polynomial `a`. -/
def C [DecidableEq R] [Zero R] (a : R) : FMvPolynomial n R :=
  if a = 0 then #[] else #[(FMonomial.zero n, a)]

end FMvPolynomial
