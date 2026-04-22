import Fettuccine.Buchberger
import Fettuccine.CMonomialOrder
import Fettuccine.CMonomialOrder.Grlex
import Fettuccine.CMonomialOrder.Grevlex
import Fettuccine.CMvPolynomial
import Fettuccine.Division
import Fettuccine.Repr

namespace Examples

abbrev σ := Fin 3

instance : Repr σ where
  reprPrec i _ := match i with
    | 0 => "x"
    | 1 => "y"
    | 2 => "z"

namespace MvPolynomial

open CMvPolynomial

def x : CMvPolynomial σ Int := X 0
def y : CMvPolynomial σ Int := X 1
def z : CMvPolynomial σ Int := X 2
def f₁ := 3*x^2 + 2*y^3 + 3*z + 1
def f₂ := 2*x^2 + 1*y^3 + 4*z
def f₃ := x^2*y^3 + 2*x*y^2 + 3*z^2 + 1

-- Render polynomials using an explicit monomial order.
#eval f₁
#eval f₁ + f₂
#eval (0 : CMvPolynomial σ Int)

-- We can also compute with polynomials.
example : 3*x^2 ≠ 0 ∧ 2*y^3 ≠ 0 ∧ 3*z + 1 ≠ 0 ∧ 1 ≠ 0 := by
  decide -- native_decide, for ℚ.

end MvPolynomial

namespace MonomialOrder

open CMonomial

def x : CMonomial σ := X 0
def y : CMonomial σ := X 1
def z : CMonomial σ := X 2

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

example : (y ≺[lex] x) := by
  decide

example : (y ≺[grevlex] x) := by
  decide

example : (x ≺[lex] x2) ∧ (xy ≺[lex] x2) ∧ (yz ≺[lex] xy)
    ∧ (xy ≺[lex] x2) ∧ (xy ≺[lex] x2 + y) := by
  decide

example : (x2 ≼[lex] x2) ∧ (yz ≼[lex] x2) := by
  decide

example : ¬(x2 ≺[lex] y3) := by
  decide

example : (xy ≺[lex] x2) ∧ (xy ≺[grlex] x2) ∧ (xy ≺[grevlex] x2) := by
  decide

example : (x ≺[grlex] y3) ∧ (x ≺[grevlex] y3) := by
  decide

example : (x2 ≺[grlex] y3) := by
  apply grlex.IsGraded -- not technically necessary... `decide` can do it too.
  decide

-- Can also obtain lex on `ℕ` with the dual order.
example : CMonomialOrder ℕᵒᵈ := lex

end MonomialOrder

namespace LeadingMonomial

open CMvPolynomial CMonomialOrder

def x : CMvPolynomial σ Int := CMvPolynomial.X 0
def y : CMvPolynomial σ Int := CMvPolynomial.X 1
def z : CMvPolynomial σ Int := CMvPolynomial.X 2

def f₁ := 3*x^2 + 2*y^3 + 3*z + 1
def f₂ : CMvPolynomial σ Int := 0

#eval f₁.leadingMonomial lex
#eval f₂.leadingMonomial lex
#eval f₁.leadingMonomial grlex
#eval f₂.leadingMonomial grlex
#eval f₁.leadingMonomial grevlex
#eval f₂.leadingMonomial grevlex

end LeadingMonomial

namespace Buchberger

set_option linter.style.nativeDecide false

open CMvPolynomial CMonomialOrder

def x : CMvPolynomial σ Rat := CMvPolynomial.X 0
def y : CMvPolynomial σ Rat := CMvPolynomial.X 1
def z : CMvPolynomial σ Rat := CMvPolynomial.X 2

-- I₁ = ⟨xy - 1, x² - y⟩
def I₁ : List (CMvPolynomial σ Rat) := [x * y - 1, x^2 - y]
def gb₁? : Option (Buchberger.GroebnerBasis I₁ CMonomialOrder.LexOrder) :=
  Buchberger.buchberger _ I₁ 32
def gb₁ := gb₁?.get (by native_decide)

#eval gb₁.basis

example : Groebner.IsGroebnerBasis CMonomialOrder.LexOrder I₁ gb₁.basis :=
  gb₁.h

-- I₂ = ⟨xy - z, xz - y, yz - x⟩
def I₂ : List (CMvPolynomial σ Rat) := [x * y - z, x * z - y, y * z - x]
def gb₂? : Option (Buchberger.GroebnerBasis I₂ CMonomialOrder.GrevlexOrder) :=
  Buchberger.buchberger _ I₂ 32
def gb₂ := gb₂?.get (by native_decide)

#eval gb₂.basis

example : Groebner.IsGroebnerBasis CMonomialOrder.GrevlexOrder I₂ gb₂.basis :=
  gb₂.h

end Buchberger

end Examples
