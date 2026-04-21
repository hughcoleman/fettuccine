import Fettuccine.Division
import Fettuccine.CMonomialOrder

/-!
# Gröbner Bases

This file defines the notion of a Gröbner basis of an ideal of `CMvPolynomial σ R`, phrased in terms
of Buchberger's criterion.

## Definitions

* `CMvPolynomial.sPolynomial ord f g` : the S-polynomial of `f` and `g`.
* `CMvPolynomial.ReducesToZero ord f gs qs` : a certificate that `f` reduces to 0 modulo the list of
  polynomials `gs`.
* `CMvPolynomial.IsGroebnerBasis ord gs` : Buchberger's criterion for a Gröbner basis.
-/

open CMonomialOrder
open scoped CMonomialOrder

namespace CMvPolynomial

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [DecidableEq R] [Field R]
variable (ord : CMonomialOrder σ)

/-- The **S-polynomial** of `f` and `g` with respect to the monomial order `ord`. -/
def sPolynomial (f g : CMvPolynomial σ R) : CMvPolynomial σ R :=
  let lm_f := in[ord](f)
  let lm_g := in[ord](g)
  -- These divisions always succeed, since the lowest common multiple is always divisible by both
  -- its factors.
  let γ   := CMonomial.lcm lm_f lm_g
  let mf  := (CMonomial.divide γ lm_f).getD 0
  let mg  := (CMonomial.divide γ lm_g).getD 0
  ofMonomial mf (leadingCoefficient ord g) * f - ofMonomial mg (leadingCoefficient ord f) * g

-- /-- The statement that a polynomial `f` reduces to zero modulo a list of divisors `gs`. -/
-- def ReducesToZero (f : CMvPolynomial σ R) (gs qs : List (CMvPolynomial σ R)) : Prop :=
--   f = (List.zipWith (· * ·) qs gs).sum ∧
--     ∀ qg ∈ List.zip qs gs, qg.1 * qg.2 = 0 ∨ in[ord](qg.1 * qg.2) ≼[ord] in[ord](f)

-- /-- The statement of Buchberger's criterion for Gröbner bases. -/
-- def IsGroebnerBasis (gs : List (CMvPolynomial σ R)) : Prop :=
--   ∀ i j : Fin gs.length, i ≠ j →
--     ∃ qs, ReducesToZero ord (sPolynomial ord (gs.get i) (gs.get j)) gs qs

end CMvPolynomial
