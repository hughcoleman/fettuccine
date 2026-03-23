import Fettuccine.CMonomialOrder
import Fettuccine.CMvPolynomial
import Fettuccine.Repr

namespace Examples

abbrev σ := Fin 3

instance : Repr σ where
  reprPrec i _ := match i with
    | 2 => "x"
    | 1 => "y"
    | 0 => "z"

namespace MvPolynomial

open CMvPolynomial

instance : CMonomialOrder σ := CMonomialOrder.lex

def x : CMvPolynomial σ Int := X 2
def y : CMvPolynomial σ Int := X 1
def z : CMvPolynomial σ Int := X 0
def f₁ := 3*x^2 + 2*y^3 + 3*z + 1
def f₂ := 2*x^2 + 1*y^3 + 4*z
def f₃ := x^2*y^3 + 2*x*y^2 + 3*z^2 + 1

#eval f₁
#eval f₁ + f₂
#eval f₁ * f₂ * f₃

-- We can also compute with polynomials.
example : 3*x^2 ≠ 0 ∧ 2*y^3 ≠ 0 ∧ 3*z + 1 ≠ 0 ∧ 1 ≠ 0 := by
  decide -- native_decide, for ℚ.

end MvPolynomial

namespace MonomialOrder

open CMonomial

def x : CMonomial σ := X 2
def y : CMonomial σ := X 1
def z : CMonomial σ := X 0

-- To be compatible with the underlying implementation, monomials are written
-- additively despite convention.
def x2 := 2 • x -- x²
def y3 := 3 • y -- y³
def xy := x + y -- xy
def yz := y + z -- yz
def xy2z := x + 2 • y + z -- xy²z

example : xy + x = y + x2 := by
  decide

-- Let's bring in special syntax for monomial orders.
open CMonomialOrder
open scoped CMonomialOrder

example : (x ≺[lex] x2) ∧ (xy ≺[lex] x2) ∧ (yz ≺[lex] xy)
    ∧ (xy ≺[lex] x2) ∧ (xy ≺[lex] x2 + y) := by
  decide

example : (x2 ≼[lex] x2) ∧ (yz ≼[lex] x2) := by
  decide

example : ¬(x2 ≺[lex] y3) := by
  decide

example : (x2 ≺[grlex] y3) := by
  apply grlex_isGraded -- not technically necessary... `decide` can do it too.
  decide

-- You can can also specifically name an instance in order to use it implicitly.
section
instance : CMonomialOrder σ := CMonomialOrder.grlex

example : (x2 ≺ y3) := by
  decide
end

-- Can also obtain lex on `CMonomial ℕ`, if you need infinite variables.
example : CMonomialOrder ℕ := lex

end MonomialOrder

namespace LeadingMonomial

open CMonomialOrder CMvPolynomial

def x : CMvPolynomial σ Int := X 2
def y : CMvPolynomial σ Int := X 1
def z : CMvPolynomial σ Int := X 0

def f₁ := 3*x^2 + 2*y^3 + 3*z + 1
def f₂ : CMvPolynomial σ Int := 0

section
instance : CMonomialOrder σ := lex
#eval f₁.leadingMonomial
#eval f₂.leadingMonomial
end

section
instance : CMonomialOrder σ := grlex
#eval f₁.leadingMonomial
#eval f₂.leadingMonomial
end

end LeadingMonomial

end Examples
