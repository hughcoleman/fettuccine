import Fettuccine.Algorithm.FMvPolynomial
import Fettuccine.Algorithm.FMonomialOrder
import Mathlib.Algebra.Field.Basic

/-!
# The Division Algorithm for Multivariate Polynomials

This file implements the division algorithm for `FMvPolynomial R` with respect to a monomial order.

## Definitions

* `untrustedMvDivide ord f gs (fuel)` : divides the polynomial `f` by the divisors `gs` with
  respect to the monomial order `ord`, constrained by `fuel` (default: 4096).
-/

namespace FMonomial

variable {n : ℕ}

/-- A decidable predicate for monomial divisibility. -/
def dvd (m₁ m₂ : FMonomial n) : Bool :=
  Vector.zipWith Nat.ble m₁ m₂ |>.all id

/-- Divide the monomial `m₁` by `m₂`, if possible. -/
def div (m₁ m₂ : FMonomial n) : Option (FMonomial n) :=
  if dvd m₂ m₁ then
    some <| Vector.zipWith Nat.sub m₁ m₂
  else
    none

end FMonomial

namespace FMvPolynomial

variable {n : ℕ}
variable {R : Type*} [DecidableEq R] [Zero R] [AddGroup R] [DivisionRing R]

variable (ord : FMonomialOrder n)

/-- Divide `f` by the divisors `gs` with respect to the monomial order `ord`. -/
def untrustedMvDivide (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R))
    -- This should be more than enough fuel for any practical example, since every division reduces
    -- the degree of the dividend by at least one, so you'd have to be working with lots of
    -- polynomials of large degree for this to begin to be an issue.
    (fuel : ℕ := 4096)
    : Array (FMvPolynomial n R) × FMvPolynomial n R :=
  loop fuel f (Array.replicate gs.size #[]) #[]
where
  /-- Find the first divisor whose leading monomial divides `lm_f`, together with the corresponding
      monomial quotient. -/
  findDivisor (lm_f : FMonomial n) : Option (Nat × FMvPolynomial n R × R × FMonomial n) :=
    Id.run do
      for h : i in [:gs.size] do
        -- An opportunity for a proof: that the index is within bounds.
        let g := gs[i]'(Membership.get_elem_helper h rfl)
        match g.leadingTerm ord with
        | none              => pure PUnit.unit
        | some (lm_g, lc_g) =>
          match FMonomial.div lm_f lm_g with
          | none   => pure PUnit.unit
          | some m => return some (i, g, lc_g, m)
      return none
  /-- Repeatedly look for a possible divisor, until `fuel` is exhausted. -/
  loop : ℕ → FMvPolynomial n R → Array (FMvPolynomial n R) → FMvPolynomial n R
      → Array (FMvPolynomial n R) × FMvPolynomial n R
    | 0, _, qs, r => (qs, r)
    | fuel + 1, f, qs, r =>
      match f.leadingTerm ord with
      | none              => (qs, r)
      | some (lm_f, lc_f) =>
        let lt := #[(lm_f, lc_f)]
        match findDivisor lm_f with
        | none =>
          -- No divisor, so move the leading term over to the accumulator.
          loop fuel (sub f lt) qs (add r lt)
        | some (i, g, lc_g, m) =>
          -- Subtract off a suitable multiple of the divisor to eliminate the leading term.
          let c   := lc_f / lc_g
          let f'  := sub f (mulMonomial m c g)
          let qs' := qs.set! i (add qs[i]! #[(m, c)])
          loop fuel f' qs' r

end FMvPolynomial
