import Fettuccine.Algorithm.Groebner
import Fettuccine.Algorithm.Buchberger
import Mathlib.Algebra.Field.Rat

-- We'll use `native_decide`; seemingly ℚ requires this...?
set_option linter.style.nativeDecide false

namespace Examples

open FMvPolynomial FMonomialOrder FMonomial

-- All of these examples will be over ℚ[x, y, z], with x > y > z.
abbrev S := FMvPolynomial 3 Rat

def m (x y z : ℕ) : FMonomial 3 :=
  { data := #[x, y, z], hsize := by simp }

section
-- ### Example: Monomial Orders
--
-- We can compare monomials under the three defined orders.

#eval lex (m 1 0 0) (m 0 1 0)  -- .gt  (x > y)
#eval lex (m 0 2 0) (m 0 1 1)  -- .gt  (y² > yz)

#eval grlex (m 0 1 0) (m 2 0 0)  -- .lt (y < x²: lower degree)
#eval grlex (m 1 1 0) (m 2 0 0)  -- .lt (xy < x²: same degree, lex)

#eval grevlex (m 1 0 0) (m 0 0 1)  -- .gt (x > z under grevlex)
#eval grevlex (m 2 0 0) (m 0 2 0)  -- .gt (x² > y² under grevlex)
end

section
-- ### Example 1: I = (xy - 1, x² - y)

def f₁ : S := #[(m 1 1 0, 1), (m 0 0 0, -1)] -- xy - 1
def f₂ : S := #[(m 2 0 0, 1), (m 0 1 0, -1)] -- x² - y

#eval (buchberger'     lex #[f₁, f₂]).map (·.map fun (m, c) => (m.toList, c))
#eval (buchberger'   grlex #[f₁, f₂]).map (·.map fun (m, c) => (m.toList, c))
#eval (buchberger' grevlex #[f₁, f₂]).map (·.map fun (m, c) => (m.toList, c))

-- We can certify the bases computed by `buchberger`, e.g. with respect to `lex`...
def gb₁ := buchberger lex #[f₁, f₂]
def cert₁ : Groebner.IsGroebnerBasis₁.Certificate lex #[f₁, f₂] gb₁.basis :=
  Groebner.IsGroebnerBasis₁.ofWitness lex #[f₁, f₂] gb₁.basis gb₁.w (by native_decide)
example : Groebner.IsGroebnerBasis₁ lex #[f₁, f₂] gb₁.basis :=
  Groebner.IsGroebnerBasis₁.sound cert₁

-- Or, with respect to `grevlex`...
def gb₂ := buchberger grevlex #[f₁, f₂]
def cert₂ : Groebner.IsGroebnerBasis₁.Certificate grevlex #[f₁, f₂] gb₂.basis :=
  Groebner.IsGroebnerBasis₁.ofWitness grevlex #[f₁, f₂] gb₂.basis gb₂.w (by native_decide)
example : Groebner.IsGroebnerBasis₁ grevlex #[f₁, f₂] gb₂.basis :=
  Groebner.IsGroebnerBasis₁.sound cert₂
end

section
-- ### Example 2: I = (xy - z, xz - y, yz - x)

def g₁ : S := #[(m 1 1 0, 1), (m 0 0 1, -1)] -- xy - z
def g₂ : S := #[(m 1 0 1, 1), (m 0 1 0, -1)] -- xz - y
def g₃ : S := #[(m 0 1 1, 1), (m 1 0 0, -1)] -- yz - x

#eval (buchberger'     lex #[g₁, g₂, g₃]).map (·.map fun (m, c) => (m.toList, c))
#eval (buchberger'   grlex #[g₁, g₂, g₃]).map (·.map fun (m, c) => (m.toList, c))
#eval (buchberger' grevlex #[g₁, g₂, g₃]).map (·.map fun (m, c) => (m.toList, c))


end

end Examples
