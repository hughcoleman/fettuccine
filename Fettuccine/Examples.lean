import Fettuccine.CMonomialOrder
import Fettuccine.CMvPolynomial
import Fettuccine.Repr

abbrev σ := Fin 3

instance : Repr σ where
  reprPrec i _ := match i with
    | 0 => "x"
    | 1 => "y"
    | 2 => "z"

namespace Examples_MvPolynomial

open CMvPolynomial

def x : CMvPolynomial σ Int := X 0
def y : CMvPolynomial σ Int := X 1
def z : CMvPolynomial σ Int := X 2

def f₁ := 3*x^2 + 2*y^3 + 3*z + 1
def f₂ := 2*x^2 + 1*y^3 + 4*z
def f₃ := x^2*y^3 + 2*x*y^2 + 3*z^2 + 1

section
instance : CMonomialOrder σ := CMonomialOrder.lex
#eval f₁ + f₂
#eval f₁ * f₂ * f₃
#eval (f₁ + f₂).leadingMonomial
#eval (f₁ * f₂ * f₃).leadingMonomial
end

section
instance : CMonomialOrder σ := CMonomialOrder.grlex
#eval f₁ + f₂
#eval f₁ * f₂ * f₃
#eval (f₁ + f₂).leadingMonomial
#eval (f₁ * f₂ * f₃).leadingMonomial
end

example : 3*x^2 ≠ 0 ∧ 2*y^3 ≠ 0 ∧ 3*z + 1 ≠ 0 ∧ 1 ≠ 0 := by
  decide

-- example : 3*x^2 ≠ 0 ∧ 2*y^3 ≠ 0 ∧ 3*z + 1 ≠ 0 ∧ 1 ≠ 0 := by
--   native_decide

end Examples_MvPolynomial

namespace Examples_MonomialOrder

open CMonomial CMonomialOrder

def x : CMonomial σ := X 0
def y : CMonomial σ := X 1
def z : CMonomial σ := X 2

def x2 := 2 • x
def y3 := 3 • y
def xy := x + y -- xy
def yz := y + z -- yz
def xy2z := x + 2 • y + z -- xy²z

#eval x2
#eval xy
#eval yz
#eval xy2z

example : xy + x = y + x2 := by
  decide

example : (x ≺[lex] x2) ∧ (xy ≺[lex] x2) ∧ (yz ≺[lex] xy)
    ∧ (xy ≺[lex] x2) ∧ (xy ≺[lex] x2 + y) := by
  decide

example : (x2 ≼[lex] x2) ∧ (yz ≼[lex] x2) := by
  decide

example : ((x2 : CMonomial σ) ≺[grlex] y3) := by
  apply grlex_isGraded -- not technically necessary
  decide

end Examples_MonomialOrder

section Examples_LeadingMonomial

open CMonomialOrder CMvPolynomial

def x : CMvPolynomial σ Int := X 0
def y : CMvPolynomial σ Int := X 1
def z : CMvPolynomial σ Int := X 2

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

end Examples_LeadingMonomial
