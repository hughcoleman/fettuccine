# fettuccine

_"It looks like one of those noodles... fettuccine?"_

A mostly-executable, self-certifying implementation of Buchberger's algorithm.

> [!CAUTION]
> For entirely unknown reasons, this implementation sometimes unpredictably segfaults Lean, especially when working with the grlex or grevlex monomial orders.
> It is recommended that you use build and execute files through the command-line, instead of VS Code.

## Building

Fettuccine is built with Lean 4.29.0, as specified in `lean-toolchain`.
It depends only on Mathlib 4.29.

To build the project, run:

```sh
lake exe cache get
lake build Fettuccine.Examples
```

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

def x : CMvPolynomial σ ℚ := CMvPolynomial.X 0
def y : CMvPolynomial σ ℚ := CMvPolynomial.X 1
def z : CMvPolynomial σ ℚ := CMvPolynomial.X 2

def I : List (CMvPolynomial σ ℚ) := [x*y - z, x*z - y, y*z - x]
def gb? : Option (Buchberger.GroebnerBasis CMonomialOrder.GrevlexOrder I) :=
  Buchberger.buchberger _ I 32
def gb := gb?.get (by native_decide)

example : Groebner.IsGroebnerBasis CMonomialOrder.GrevlexOrder I gb.basis :=
  gb.h

#eval gb.basis
```

This produces:

```
[y*x + -1*z, z*x + -1*y, -1*x + z*y, y^2 + -1*z^2, x^2 + -1*z^2, z^3 + -1*z]
```

In fact, this happens to be a reduced Gr&ouml;bner basis&mdash;but, in general, this implementation does not always produce a reduced basis.

## Overview

### Multivariate Polynomials

The files [CMvPolynomial.lean](Fettuccine/CMvPolynomial.lean) and [CMonomialOrder.lean](Fettuccine/CMonomialOrder.lean) define the types `CMonomial`, `CMvPolynomial`, and `CMonomialOrder`, which are the primary mathematical types used.
Here, we also develop `leadingMonomial`, `leadingCoefficient`, and `leadingTerm`, as well as concrete instances of the well-founded monomial orders [`lex`](Fettuccine/CMonomialOrder.lean), [`grlex`](Fettuccine/CMonomialOrder/Grlex.lean), and [`grevlex`](Fettuccine/CMonomialOrder/Grevlex.lean).

### Gr&ouml;bner Bases

[Groebner.lean](Fettuccine/Groebner.lean) contains the mathematical specifications of Gr&ouml;bner bases.
It defines S-polynomials (as `sPolynomial` and `sPolynomial'`), reduction predicates such as `ReducesToZero`, the generated ideal `idealOf`, and the predicate `IsGroebnerBasis`.
This is the interface against which computed candidate bases are checked.

### Fast, Executable Buchberger's Algorithm

The `Fettuccine/Algorithm/` folder contains the fast array-based implementation intended for `#eval` and `native_decide`.
Here, monomials and polynomials are represented by `FMonomial` and `FMvPolynomial`, together with executable monomial orders in [FMonomialOrder.lean](Fettuccine/Algorithm/FMonomialOrder.lean), executable division in [Division.lean](Fettuccine/Algorithm/Division.lean), and Buchberger's algorithm in [Buchberger.lean](Fettuccine/Algorithm/Buchberger.lean).
It provides `untrustedBuchberger`.

### Bridging and Certification

[Buchberger.lean](Fettuccine/Buchberger.lean) bridges the fast layer and the mathematical layer by converting between `CMvPolynomial` and `FMvPolynomial`, re-packaging witnesses, and exposing the proof-bearing `GroebnerBasis` structure together with the user-facing `buchberger` function.
[Repr.lean](Fettuccine/Repr.lean) supplies readable output for examples, and [Examples.lean](Fettuccine/Examples.lean) demonstrates a handful of worked computations.

### Multivariate Polynomial Division Theory

[Division.lean](Fettuccine/Division.lean) develops the formal theory of multivariate polynomial division for `CMvPolynomial`.
It defines monomial divisibility `dvd`, quotient computation `div`, the specification `IsMvQuotientRemainder`, the division algorithm `mvDivide`, and its correctness theorem `mvDivide_spec`.
This file is one of the only proof-theoretic accomplishments of the project: it gives a machine-checked account of polynomial division.
It is, however, wildly unstable to execute; the implementation of Buchberger's algorithm relies on the array-based procedures in `Fettuccine/Algorithm/`.
