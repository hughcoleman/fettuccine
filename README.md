# fettuccine

_"It looks like one of those noodles... fettuccine?"_

A mostly-executable, self-certifying implementation of Buchberger's algorithm.
It is implemented in Lean 4.29, and, other than Mathlib 4.29, has no external dependencies.

> [!CAUTION]
> For entirely unknown reasons, this implementation sometimes unpredictably segfaults Lean, especially when working with the grlex or grevlex monomial orders.

## Example

We can compute a Gr&ouml;bner basis for the ideal $$I = (x y - z, x z - y, y z - x)$$ with respect to the grevlex order as follows.

```lean
import Fettuccine.Buchberger
import Fettuccine.CMonomialOrder
import Fettuccine.CMonomialOrder.Grlex
import Fettuccine.CMonomialOrder.Grevlex
import Fettuccine.CMvPolynomial
import Fettuccine.Repr

set_option linter.style.nativeDecide false

abbrev σ := Fin 3

instance : Repr σ where
  reprPrec i _ := match i with
    | 0 => "x"
    | 1 => "y"
    | 2 => "z"

open CMvPolynomial CMonomialOrder

def x : CMvPolynomial σ Rat := CMvPolynomial.X 0
def y : CMvPolynomial σ Rat := CMvPolynomial.X 1
def z : CMvPolynomial σ Rat := CMvPolynomial.X 2

def I : List (CMvPolynomial σ Rat) := [x * y - z, x * z - y, y * z - x]
def gb? : Option (Buchberger.GroebnerBasis I CMonomialOrder.GrevlexOrder) :=
  Buchberger.buchberger _ I 32
def gb := gb?.get (by native_decide)

example : Groebner.IsGroebnerBasis CMonomialOrder.GrevlexOrder I gb.basis :=
  gb.h

#eval gb.basis
-- [yx + -1*z, zx + -1*y, -1*x + zy, y^2 + -1*z^2, x^2 + -1*z^2, z^3 + -1*z]
```

This is, in fact, a reduced Gr&ouml;bner basis&mdash;but, in general, this implementation does not always produce a reduced basis.
