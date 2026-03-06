import Groebner.GroebnerBasis.CMvPolynomial.CMvPolynomial

/-!
# Monomial orders

This file defines computable monomial orders and provides the instances `Lex`,
`Grlex`, and `Grevlex`.
-/

namespace MonomialOrder

/-- A computable total order on `CMonomial σ`.  -/
structure CMonomialOrder (σ : Type*) where
  lt : CMonomial σ → CMonomial σ → Bool

-- TODO:
-- [ ] Proof that a CMonomialOrder is a MonomialOrder.


end MonomialOrder
