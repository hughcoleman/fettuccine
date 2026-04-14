import Fettuccine.CMvPolynomial
import Fettuccine.CMonomialOrder
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.DFinsupp.Lex
import Mathlib.Data.Finset.Sort

/-- An instance of `Repr` for `Fin n`, displaying as x₀, x₁, etc. -/
instance Fin.fallbackRepr {n : ℕ} : Repr (Fin n) where
  reprPrec i _ := "x" ++ String.map digits (toString i.val)
where
  digits : Char → Char
    | '0' => '₀' | '1' => '₁' | '2' => '₂' | '3' => '₃' | '4' => '₄'
    | '5' => '₅' | '6' => '₆' | '7' => '₇' | '8' => '₈' | '9' => '₉'
    | c   => c

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ] [Repr σ]

/-- Display a monomial. -/
instance : Repr (CMonomial σ) where
  reprPrec m _ :=
    let terms := m.support.sort (· ≥ ·)
      |>.filterMap fun x =>
        match m x with
        | 0 => none
        | 1 => some f!"{reprPrec x 0}"
        | e => some f!"{reprPrec x 0}^{e}"
    if terms.isEmpty then "1"
    else
      Std.Format.joinSep terms ""

variable {R : Type*} [DecidableEq R] [CommSemiring R] [Repr R]

open CMonomialOrder
open scoped CMonomialOrder

-- /-- Display a multivariate polynomial. -/
-- instance [WellFoundedGT σ] : Repr (CMvPolynomial σ R) where
--   reprPrec f _ :=
--     haveI : LinearOrder (CMonomial σ) := LinearOrder.lift'
--       (fun m => toLex m.toFun)
--       (fun m₁ m₂ h => by cases m₁; cases m₂; simp_all)
--     haveI : DecidableRel fun x1 x2 ↦ x1 ≤ x2 := by
--       sorry
--     haveI : Std.Antisymm fun x1 x2 ↦ x1 < x2 := by
--       sorry
--     haveI : Std.Total fun x1 x2 ↦ x1 < x2 := by
--       sorry
--     let terms := f.toFun.support.sort (· ≤ ·)
--       |>.filterMap fun m =>
--         let coeff := f m
--         if      coeff == 0 then none
--         else if coeff == 1 then some (reprPrec m 0)
--         else                    some f!"{reprPrec coeff 0}{reprPrec m 0}"
--     if terms.isEmpty then "0"
--     else
--       Std.Format.joinSep terms " + "
