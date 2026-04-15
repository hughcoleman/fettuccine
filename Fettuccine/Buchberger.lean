import Fettuccine.Divide
import Fettuccine.CMonomialOrder
import Fettuccine.CMvPolynomial

/-!
# Buchberger's Algorithm

This file defines Buchberger's algorithm for computing Gröbner bases for ideals of
`CMvPolynomial σ R`.

## Definitions

* `sPolynomial f g` : the S-polynomial of two polynomials `f` and `g`.
-/

section SPolynomial

variable {σ : Type*} [DecidableEq σ] (ord : CMonomialOrder σ)
variable {R : Type*} [DecidableEq R] [CommRing R]

namespace CMvPolynomial

/-- The **S-polynomial** of two polynomials, with respect to the monomial order `ord`, as defined by
    Buchberger. -/
def sPolynomial (f g : CMvPolynomial σ R) : CMvPolynomial σ R :=
  let l := CMonomial.lcm (lm[ord](f)) (lm[ord](g))
  -- Each leading monomial divides their lowest common multiple, so the quotients necessarily exist.
  have hf : (l.divide (lm[ord](f))).isSome := by
    have hdiv : CMonomial.divides? (lm[ord](f)) l :=
      CMonomial.divides?_lcm_left (lm[ord](f)) (lm[ord](g))
    simp [CMonomial.divide, hdiv]
  have hg : (l.divide (lm[ord](g))).isSome := by
    have hdiv : CMonomial.divides? (lm[ord](g)) l :=
      CMonomial.divides?_lcm_right (lm[ord](f)) (lm[ord](g))
    simp [CMonomial.divide, hdiv]
  -- Use those quotients to scale f and g to a common leading monomial, and then subtract.
  let mf := Option.get (l.divide (lm[ord](f))) hf
  let mg := Option.get (l.divide (lm[ord](g))) hg
  CMvPolynomial.ofMonomial mf (leadingCoefficient ord g) * f -
    CMvPolynomial.ofMonomial mg (leadingCoefficient ord f) * g

end CMvPolynomial

end SPolynomial
