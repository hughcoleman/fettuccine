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

/-- A monomial on `n` variables is represented as a fixed-length exponent vector. -/
abbrev FMonomial (n : ℕ) := Vector ℕ n

namespace FMonomial

variable {n : ℕ}

/-- The zero monomial on `n` variables. -/
def zero (n : ℕ) : FMonomial n :=
  Vector.replicate n 0

/-- The monomial `xᵢ`: exponent 1 at position `i`, 0 elsewhere. -/
def X (i : Fin n) : FMonomial n := {
  toArray      := Array.ofFn fun i₀ : Fin n =>
                    if i₀ = i then 1 else 0
  size_toArray := by simp
}

/-- The **degree** of a monomial, which is the sum of the degrees in each variable. -/
def degree (m : FMonomial n) : ℕ := m.toArray.foldl (· + ·) 0

/-- The **product** of two monomials, which is given by the pointwise sum of exponents. -/
-- We'll match the terminology with `CMonomial`, and refer to this operation as "addition" and not
-- "multiplication".
def add (m₁ m₂ : FMonomial n) : FMonomial n :=
  Vector.zipWith Nat.add m₁ m₂

/-- The **lowest common multiple** of two monomials, which is given by the pointwise maximum of
    exponents. -/
def lcm (m₁ m₂ : FMonomial n) : FMonomial n :=
  Vector.zipWith Nat.max m₁ m₂

/-- Two monomials are said to be **coprime** or **relatively prime** if they share no common
    variables with positive exponents. -/
def isCoprime (m₁ m₂ : FMonomial n) : Bool :=
  Vector.zipWith (fun a b => a == 0 || b == 0) m₁ m₂ |>.all id

section Examples

private abbrev m (a b c : ℕ) : FMonomial 3 :=
  Vector.mk #[a, b, c] (by simp)

example : degree (m 1 2 3) = 6 := by
  rfl

-- All of these can also be discharged via `native_decide`, since they are trivially decidable
-- statements.

example : add (m 1 2 3) (m 4 5 6) = (m 5 7 9) := by
  simp [FMonomial.add]

example : lcm (m 1 2 3) (m 4 5 6) = (m 4 5 6) := by
  simp [FMonomial.lcm]

example : isCoprime (m 1 0 2) (m 0 3 0) := by
  simp [FMonomial.isCoprime]

example : ¬ isCoprime (m 1 1 2) (m 0 3 0) := by
  simp [FMonomial.isCoprime]

end Examples

end FMonomial

/-- A multivariate polynomial, represented as an array of monomial-coefficient pairs. Terms are not
    stored in any particular order, but will generally be assumed to be irredundant. The `normalize`
    function in FMonomialOrder.lean can be used to perform normalization. -/
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

instance instOfNat [DecidableEq R] [Zero R] {k : ℕ} [OfNat R k] : OfNat (FMvPolynomial n R) k :=
  ⟨C (OfNat.ofNat k)⟩

end FMvPolynomial
