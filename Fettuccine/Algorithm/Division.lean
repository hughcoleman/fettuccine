import Fettuccine.Algorithm.FMvPolynomial
import Fettuccine.Algorithm.FMonomialOrder
import Mathlib.Algebra.Field.Basic

/-!
# The Division Algorithm for Multivariate Polynomials

This file implements the simultaneous multiple-divisor division algorithm for `FMvPolynomial R` with
respect to a monomial order.

## Definitions

* `untrustedMvDivide ord f gs fuel` : divides the polynomial `f` by the divisors `gs` with respect
  to the monomial order `ord`, constrained by `fuel` (default: 4096).
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

lemma dvd_iff_div_eq (m₁ m₂ : FMonomial n) : dvd m₂ m₁ = true ↔ (div m₁ m₂).isSome := by
  simp [div]

lemma not_dvd_iff_div_eq (m₁ m₂ : FMonomial n) :
    div m₁ m₂ = none ↔ dvd m₂ m₁ = false := by
  simp [div]

lemma div_wellDefined {m₁ m₂ : FMonomial n} (h : m₂.dvd m₁) :
    ∃ q, div m₁ m₂ = some q ∧ FMonomial.add q m₂ = m₁ := by
  refine ⟨Vector.zipWith Nat.sub m₁ m₂, by simp [div, h], ?_⟩
  apply Vector.ext
  -- By assumption, each component of `m₂` is less than or equal to the corresponding component of
  -- `m₁`.
  have h_all : (Vector.zipWith Nat.ble m₂ m₁).all id = true := by
    simpa [FMonomial.dvd] using (show m₂.dvd m₁ = true by simpa using h)
  -- Pass to a component-wise statement.
  intro i hi
  have hle : m₂[i] ≤ m₁[i] := by
    exact Nat.ble_eq.mp <| by
      simpa [Vector.getElem_zipWith] using
        (Array.all_eq_true.mp h_all) i (by simpa using hi)
  simp [FMonomial.add, Vector.getElem_zipWith, hle, Nat.sub_add_cancel]

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

/-- Zero divided by anything is zero; an easy statement to prove even for this implementation of
    Buchberger's algorithm. -/
lemma untrustedMvDivide_zero (ord : FMonomialOrder n) (gs : Array (FMvPolynomial n R)) :
    untrustedMvDivide ord zero gs =
      (Array.replicate gs.size zero, zero) := by
  rfl

end FMvPolynomial
