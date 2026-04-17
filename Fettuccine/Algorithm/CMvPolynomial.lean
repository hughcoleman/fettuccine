import Mathlib.Algebra.Group.Basic

/-!
# Computable Multivariate Polynomials

This file defines the types `CMonomial n` and `CMvPolynomial n R`, which are computable
representations of monomials (`Monomial σ`) and multivariate polynomials (`MvPolynomial σ R`).

## Definitions

- `CMonomial n` : the type of monomials on `n` variables; `m[i]` is the exponent of variable `i`.
- `CMonomial.X i` : the monomial `xᵢ` (variable `i` with exponent 1).
- `CMvPolynomial n R` : normalized array of `(monomial, coefficient)` pairs.
- `CMvPolynomial.X i` : the polynomial `xᵢ`.
- `CMvPolynomial.C a` : the constant polynomial with value `a`.
-/

/-- A monomial on `n` variables is represented as an array of exponents alongside a proof that it is
    of the expected length. -/
structure CMonomial (n : ℕ) where
  data : Array ℕ
  hsize : data.size = n
deriving DecidableEq

namespace CMonomial

variable {n : ℕ}

@[simp] theorem size_data (m : CMonomial n) : m.data.size = n := m.hsize

/-- Convert a monomial to its exponent list. -/
def toList (m : CMonomial n) : List ℕ := m.data.toList

/-- The zero monomial on `n` variables. -/
def zero (n : ℕ) : CMonomial n where
  data := Array.replicate n 0
  hsize := by simp

/-- The monomial `xᵢ`: exponent 1 at position `i`, 0 elsewhere. -/
def X (i : Fin n) : CMonomial n where
  data := Array.ofFn (fun j : Fin n => if j = i then 1 else 0)
  hsize := by simp

/-- The degree of a monomial. -/
def degree (m : CMonomial n) : ℕ := m.data.foldl (· + ·) 0

/-- The product of two monomials (component-wise addition of exponents). -/
def add (m₁ m₂ : CMonomial n) : CMonomial n where
  data := Array.zipWith (· + ·) m₁.data m₂.data
  hsize := by simp [m₁.hsize, m₂.hsize]

/-- The lowest common multiple of two monomials (component-wise maximum of exponents). -/
def lcm (m₁ m₂ : CMonomial n) : CMonomial n where
  data := Array.zipWith max m₁.data m₂.data
  hsize := by simp [m₁.hsize, m₂.hsize]

end CMonomial

/-- A multivariate polynomial, represented as an array of monomial-coefficient pairs, stored sorted
    according to a (fixed, implicit) monomial order. -/
abbrev CMvPolynomial (n : ℕ) (R : Type*) := Array (CMonomial n × R)

namespace CMvPolynomial

variable {n : ℕ}
variable {R : Type*}

/-- The zero polynomial. -/
def zero : CMvPolynomial n R := #[]

/-- The polynomial `xᵢ`. -/
def X [One R] (i : Fin n) : CMvPolynomial n R := #[(CMonomial.X i, 1)]

/-- The constant polynomial `a`. -/
def C [DecidableEq R] [Zero R] (a : R) : CMvPolynomial n R :=
  if a = 0 then #[] else #[(CMonomial.zero n, a)]

end CMvPolynomial
