import Fettuccine.CMonomialOrder
import Fettuccine.CMvPolynomial

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

#eval f₁ + f₂
#eval f₁ * f₂ * f₃

example : 3*x^2 ≠ 0 ∧ 2*y^3 ≠ 0 ∧ 3*z + 1 ≠ 0 ∧ 1 ≠ 0 := by
  decide

example : 3*x^2 ≠ 0 ∧ 2*y^3 ≠ 0 ∧ 3*z + 1 ≠ 0 ∧ 1 ≠ 0 := by
  native_decide

end Examples_MvPolynomial

namespace Examples_MonomialOrder

open CMonomial CMonomialOrder

def x : CMonomial σ := X 0
def y : CMonomial σ := X 1
def z : CMonomial σ := X 2

def x2 := 2 • x
def xy := x + y -- xy
def yz := y + z -- yz
def xy2z := x + 2 • y + z -- xy²z

#eval x2
#eval xy
#eval yz
#eval xy2z

example : xy + x = y + x2 := by
  decide

example : (x ≺[Lex.lex] x2) ∧ (xy ≺[Lex.lex] x2) ∧ (yz ≺[Lex.lex] xy)
    ∧ (xy ≺[Lex.lex] x2) ∧ (xy ≺[Lex.lex] x2 + y) := by
  split_ands
  all_goals rw [CMonomialOrder.lt']; decide

example : (x2 ≼[Lex.lex] x2) ∧ (yz ≼[Lex.lex] x2) := by
  split_ands
  all_goals rw [CMonomialOrder.le']
  decide

end Examples_MonomialOrder

section Examples_LeadingMonomial

open CMonomialOrder CMvPolynomial

def x : CMvPolynomial σ Int := X 0
def y : CMvPolynomial σ Int := X 1
def z : CMvPolynomial σ Int := X 2

def f₁ := 3*x^2 + 2*y^3 + 3*z + 1
def f₂ : CMvPolynomial σ Int := 0

#eval f₁.leadingMonomial Lex.lex
#eval f₂.leadingMonomial Lex.lex

end Examples_LeadingMonomial
