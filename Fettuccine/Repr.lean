import Fettuccine.CMonomialOrder
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

namespace CMvPolynomial

universe u v w

/-- A polynomial paired with a monomial order for pretty-printing. -/
structure Ordered (σ : Type u) [DecidableEq σ] (R : Type v) [CommSemiring R] where
  /-- The polynomial to display. -/
  f : CMvPolynomial σ R
  /-- The monomial order used to sort terms while displaying. -/
  ord : CMonomialOrder.{u, w} σ

/-- Wrap `f` with `ord` so it can be rendered in that monomial order. -/
def withOrdering {σ : Type u} [DecidableEq σ] {R : Type v} [CommSemiring R]
  (f : CMvPolynomial σ R) (ord : CMonomialOrder σ) : Ordered σ R :=
  ⟨f, ord⟩

instance {σ : Type u} [DecidableEq σ] {R : Type v} [CommSemiring R] :
    Coe (Ordered σ R) (CMvPolynomial σ R) where
  coe := Ordered.f

/-- Display a multivariate polynomial with terms ordered by `w.ord`. -/
instance {σ : Type u} [DecidableEq σ] [LinearOrder σ] [Repr σ]
    {R : Type v} [DecidableEq R] [CommSemiring R] [Repr R] : Repr (Ordered σ R) where
  reprPrec w _ :=
    let rel : CMonomial σ → CMonomial σ → Prop :=
      fun m₁ m₂ => w.ord.toSyn m₁ ≤ w.ord.toSyn m₂
    -- We need to show that `rel` is a linear order, so that we can use it to sort the monomials.
    letI : Std.Total rel :=
      ⟨fun x y => le_total (w.ord.toSyn x) (w.ord.toSyn y)⟩
    letI : Std.Antisymm rel :=
      ⟨fun _ _ hxy hyx => w.ord.toSyn.injective (le_antisymm hxy hyx)⟩
    letI : IsTrans (CMonomial σ) rel :=
      ⟨fun _ _ _ hxy hyz => le_trans hxy hyz⟩
    -- Sort the monomials by `rel` and display them each appropriately.
    let terms := (w.f.support.sort rel).reverse
      |>.filterMap fun m =>
        let coeff := w.f.coefficientOf m
        if coeff = 0      then none
        else if m = 0     then some f!"{reprPrec coeff 0}"
        else if coeff = 1 then some f!"{reprPrec m 0}"
        else                   some f!"{reprPrec coeff 0}*{reprPrec m 0}"
    if terms.isEmpty then "0"
    else
      Std.Format.joinSep terms " + "

end CMvPolynomial
