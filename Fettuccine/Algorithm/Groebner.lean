import Fettuccine.Algorithm.FMonomialOrder
import Mathlib.Algebra.Field.Rat

/-!
# Gröbner Bases

This file defines the notion of a Gröbner basis for ideals of `MvPolynomial σ R` with respect to a
monomial order.
-/

variable {n : ℕ}

def IsGroebnerBasis (ord : FMonomialOrder (n := n))
    (gens : Array (FMvPolynomial n ℚ))
  : Prop := sorry
