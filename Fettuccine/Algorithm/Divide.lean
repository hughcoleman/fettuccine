import Fettuccine.Algorithm.CMvPolynomial
import Fettuccine.Algorithm.CMonomialOrder
import Mathlib.Algebra.Field.Basic

/-!
# The Division Algorithm for Multivariate Polynomials

This file implements the division algorithm for `CMvPolynomial R` with respect to a monomial order.

## Definitions

* `divide ord f gs fuel` : divides `f` by the divisors `gs` with respect to the monomial order
  `ord`, constrained by `fuel`.
* `divide₁ ord f g fuel` : divides `f` by `g` with respect to the monomial order `ord`.
-/

namespace CMonomial

variable {n : ℕ}

-- A decidable predicate for monomial divisibility.
def divides? (m₁ m₂ : CMonomial n) : Bool :=
  Id.run do
    for i in [:n] do
      if !(Nat.ble (m₁.data.getD i 0) (m₂.data.getD i 0)) then
        return false
    return true

/-- Divide the monomial `m₁` by `m₂`, if possible. -/
def divide (m₁ m₂ : CMonomial n) : Option (CMonomial n) :=
  if divides? m₂ m₁ then
    some {
      data := Array.zipWith (· - ·) m₁.data m₂.data
      hsize := by simp [m₁.hsize, m₂.hsize]
    }
  else
    none

end CMonomial

namespace CMvPolynomial

variable {n : ℕ}
variable {R : Type*} [DecidableEq R] [Zero R] [AddGroup R] [DivisionRing R]

/-- Divide `f` by the divisors `gs` with respect to the monomial order `ord`. -/
-- NOTE: `gs` is assumed to be a non-empty array of normalized, non-zero polynomials.
def mvDivide (ord : CMonomial n → CMonomial n → Ordering)
    (f : CMvPolynomial n R) (gs : Array (CMvPolynomial n R)) (fuel : ℕ := 4096) -- should be enough
    : Array (CMvPolynomial n R) × CMvPolynomial n R :=
  loop fuel f (Array.replicate gs.size #[]) #[]
where
  /-- Find the first divisor whose leading monomial divides `lm_f`, together with the corresponding
      monomial quotient. -/
  findDivisor (lm_f : CMonomial n) : Option (Nat × CMvPolynomial n R × R × CMonomial n) :=
    Id.run do
      for i in [:gs.size] do
        let g := gs[i]!
        match g.leadingTerm with
        | none => pure PUnit.unit
        | some (lm_g, lc_g) =>
          match CMonomial.divide lm_f lm_g with
          | none   => pure PUnit.unit
          | some m => return some (i, g, lc_g, m)
      return none
  /-- Repeatedly look for divisors, until `fuel` is exhausted. -/
  loop : ℕ → CMvPolynomial n R → Array (CMvPolynomial n R) → CMvPolynomial n R
      → Array (CMvPolynomial n R) × CMvPolynomial n R
    | 0, _, qs, r => (qs, r)
    | fuel + 1, f, qs, r =>
      match f.leadingTerm with
      | none              => (qs, r)
      | some (lm_f, lc_f) =>
        let lt := #[(lm_f, lc_f)]
        match findDivisor lm_f with
        | none =>
          -- No divisor, so move the leading term over to the accumulator.
          loop fuel (sub ord f lt) qs (add ord r lt)
        | some (i, g, lc_g, m) =>
          -- Subtract off a suitable multiple of the divisor to eliminate the leading term.
          let c   := lc_f / lc_g
          let f'  := sub ord f (mulMonomial ord m c g)
          let qs' := qs.set! i (add ord qs[i]! #[(m, c)])
          loop fuel f' qs' r

/-- Divide `f` by a single divisor `g`. -/
def mvDivide₁ (ord : CMonomial n → CMonomial n → Ordering)
    (f g : CMvPolynomial n R) (fuel : ℕ := 4096) : CMvPolynomial n R × CMvPolynomial n R :=
  let (qs, r) := mvDivide ord f #[g] fuel
  (qs.getD 0 #[], r)

end CMvPolynomial
