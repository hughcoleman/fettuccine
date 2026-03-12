import Fettuccine.GroebnerBasis.MvPolynomial.CMvPolynomial

import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.TFAE

/-!
# Monomial orders

This file defines computable monomial orders and provides the orders `Lex`,
`Grlex`, and `Grevlex` on monomials.
-/

/-- A computable total order on `CMonomial σ`. -/
structure CMonomialOrder (σ : Type*) [LinearOrder σ] where
  lt : CMonomial σ → CMonomial σ → Bool

namespace MonomialOrder

variable {σ : Type*} [LinearOrder σ]

def le (m : CMonomialOrder σ) (a b : CMonomial σ) : Bool :=
  m.lt a b || a = b

/-- Notation for the ordering relation on `CMonomial σ`. -/
notation:50 lhs " ≺[" m:25 "] " rhs:50 => (CMonomialOrder.lt  m lhs rhs)
notation:50 lhs " ≼[" m:25 "] " rhs:50 => (CMonomialOrder.lte m lhs rhs)

end MonomialOrder

/-- The lexicographic order on monomials. -/
instance lex (σ : Type*) [LinearOrder σ] : CMonomialOrder σ where
  lt a b := sorry

/-- The graded lexicographic order on monomials. -/
instance grlex (σ : Type*) [LinearOrder σ] : CMonomialOrder σ where
  lt a b := sorry

/-- The graded reverse lexicographic order on monomials. -/
instance grevlex (σ : Type*) [LinearOrder σ] : CMonomialOrder σ where
  lt a b := sorry
