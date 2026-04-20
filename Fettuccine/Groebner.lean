import Fettuccine.Divide
import Fettuccine.MonomialOrder

/-!
# Gröbner Bases

This file defines the notion of a Gröbner basis of an ideal of `MvPolynomial σ R`, phrased in terms
of Buchberger's criterion.

## Definitions

* `MvPolynomial.sPolynomial ord f g` : the S-polynomial of `f` and `g`.
* `MvPolynomial.ReducesToZero ord f gs qs` : a certificate that `f` reduces to 0 modulo the list of
  polynomials `gs`.
* `MvPolynomial.IsGroebnerBasis ord gs` : Buchberger's criterion for a Gröbner basis.
-/

open MonomialOrder
open scoped MonomialOrder

namespace MvPolynomial

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [DecidableEq R] [Field R]
variable (ord : MonomialOrder σ)

/-- The **S-polynomial** of `f` and `g` with respect to the monomial order `ord`. -/
def sPolynomial (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  let lm_f := in[ord](f)
  let lm_g := in[ord](g)
  -- These divisions always succeed, since the lowest common multiple is always divisible by both
  -- its factors.
  let γ   := Monomial.lcm lm_f lm_g
  let mf  := (Monomial.divide γ lm_f).getD 0
  let mg  := (Monomial.divide γ lm_g).getD 0
  ofMonomial mf (leadingCoefficient ord g) * f - ofMonomial mg (leadingCoefficient ord f) * g

-- /-- The statement that a polynomial `f` reduces to zero modulo a list of divisors `gs`. -/
-- def ReducesToZero (f : MvPolynomial σ R) (gs qs : List (MvPolynomial σ R)) : Prop :=
--   f = (List.zipWith (· * ·) qs gs).sum ∧
--     ∀ qg ∈ List.zip qs gs, qg.1 * qg.2 = 0 ∨ in[ord](qg.1 * qg.2) ≼[ord] in[ord](f)

-- /-- The statement of Buchberger's criterion for Gröbner bases. -/
-- def IsGroebnerBasis (gs : List (MvPolynomial σ R)) : Prop :=
--   ∀ i j : Fin gs.length, i ≠ j →
--     ∃ qs, ReducesToZero ord (sPolynomial ord (gs.get i) (gs.get j)) gs qs

end MvPolynomial
