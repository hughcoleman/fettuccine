import Fettuccine.Algorithm.Divide
import Fettuccine.Algorithm.LinearCombination

/-!
# Gröbner Bases

This file defines proof-bearing and witness-checked certificates for Gröbner bases in the
array-backed polynomial model.
-/

namespace FMvPolynomial

variable {n : ℕ}
variable {R : Type*} [DecidableEq R] [Zero R] [AddGroup R] [DivisionRing R]

/-- The **S-polynomial** of two (non-zero) polynomials `f` and `g` with respect to the monomial
    order `ord`. -/
-- S(f, g) = (l / lm_f) * lc_g * f - (l / lm_g) * lc_f * g
--         = lcm(lm_f, lm_g) / lm_f * lc_g * f - lcm(lm_f, lm_g) / lm_g * lc_f * g
def sPolynomial (ord : FMonomialOrder n) (f g : FMvPolynomial n R) : FMvPolynomial n R :=
  match f.leadingTerm ord, g.leadingTerm ord with
  | some (lm_f, lc_f), some (lm_g, lc_g) =>
    -- These divisions necessarily always succeed because the lowest common multiple is
    -- definitionally divisible by both.
    let lcm := FMonomial.lcm lm_f lm_g
    let mf := (lcm.divide lm_f).getD (FMonomial.zero n)
    let mg := (lcm.divide lm_g).getD (FMonomial.zero n)
    sub (mulMonomial mf lc_g f) (mulMonomial mg lc_f g)
  | _, _ =>
    -- If either polynomial is zero, the S-polynomial is conventionally taken to be zero. (This
    -- generally doesn't come up in practice.)
    FMvPolynomial.zero

end FMvPolynomial

namespace Groebner

open FMvPolynomial

variable {n : ℕ}
variable {R : Type*} [DecidableEq R] [Zero R] [AddGroup R] [DivisionRing R]

-- To witness a Groebner basis, we need to provide proofs that the basis elements belong to the
-- ideal, and, that each S-polynomial reduces to zero.
abbrev BasisMembershipWitnesses (n : ℕ) :=
  Array (Array (FMvPolynomial n R))
abbrev SPolynomialsReductionWitnesses (n : ℕ) :=
  Array (Array (Array (FMvPolynomial n R)))

structure Witness (n : ℕ) (R : Type*) where
  bm : BasisMembershipWitnesses (R := R) n
  sr : SPolynomialsReductionWitnesses (R := R) n

open Division
open LinearCombination

/-- Check a Gröbner basis witness. -/
def IsGroebnerBasisWith (ord : FMonomialOrder n) (gens : Array (FMvPolynomial n R))
    -- The proposed basis, alongside witnesses.
    (basis : Array (FMvPolynomial n R)) (witness : Witness n R) : Prop :=
  -- Every element of the basis must lie in the ideal; i.e. be a polynomial linear combination of
  -- the generators.
  ∃ h₁ : basis.size = witness.bm.size,
    (∀ i : Fin basis.size,
      let cs := witness.bm[i.val]'(by rw [← h₁]; exact i.2)
      IsLinearCombinationWith basis[i] gens cs) ∧
  ∃ h₂ : basis.size = witness.sr.size,
    ∀ i : Fin basis.size,
      let C := witness.sr[i.val]'(by rw [← h₂]; exact i.2)
      ∃ h₂' : basis.size = C.size,
        ∀ j : Fin basis.size, i < j →
          let qs := C[j.val]'(by rw [← h₂']; exact j.2)
          ReducesToZeroWith ord (sPolynomial ord basis[i] basis[j]) basis qs

instance decidableIsGroebnerBasisWith (ord : FMonomialOrder n) (gens : Array (FMvPolynomial n R))
    (basis : Array (FMvPolynomial n R)) (witness : Witness n R) :
    Decidable (IsGroebnerBasisWith ord gens basis witness) := by
  unfold IsGroebnerBasisWith
  infer_instance

/-- Buchberger's characterization of Gröbner bases. -/
def IsGroebnerBasis₁ (ord : FMonomialOrder n) (gens : Array (FMvPolynomial n R))
    (basis : Array (FMvPolynomial n R)) : Prop :=
  ∃ witness : Witness n R, IsGroebnerBasisWith ord gens basis witness

namespace IsGroebnerBasis₁

structure Certificate (ord : FMonomialOrder n) (gens : Array (FMvPolynomial n R))
    (basis : Array (FMvPolynomial n R)) where
  witness : Witness n R
  h : IsGroebnerBasisWith ord gens basis witness

theorem sound {ord : FMonomialOrder n} {gens : Array (FMvPolynomial n R)}
    {basis : Array (FMvPolynomial n R)} (cert : Certificate ord gens basis) :
    IsGroebnerBasis₁ ord gens basis :=
  ⟨cert.witness, cert.h⟩

/-- Construct a certificate from a witness. -/
def ofWitness (ord : FMonomialOrder n) (gens : Array (FMvPolynomial n R))
    (basis : Array (FMvPolynomial n R)) (witness : Witness n R)
    (h : decide (IsGroebnerBasisWith ord gens basis witness) = true) :
    Certificate ord gens basis :=
  { witness := witness
    h       := of_decide_eq_true h }

end IsGroebnerBasis₁

end Groebner
