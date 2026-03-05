import Groebner.CMvPolynomial

/-!
# Computable Monomial Orders

This file defines the type `CMonomialOrder σ` — a computable total order on
`CMonomial σ` — and provides three standard instances:

* `CMonomialOrder.lex` — pure lexicographic order
* `CMonomialOrder.grlex` — graded lexicographic order
* `CMonomialOrder.grevlex` — graded reverse lexicographic order

It also contains the **order-dependent** operations on `CMvPolynomial σ R`:
`leadMon`, `leadCoeff`, `leadTerm`, and `tail`.  These live here (rather than
in `CMvPolynomial.lean`) to avoid pulling the order machinery into the base file.
-/

-- ============================================================
-- CMonomialOrder
-- ============================================================

/-- A computable total order on `CMonomial σ`.

    `ord.lt a b = true` means `a < b` (i.e. `b` is "bigger" in the order).
    The order is expected to be a monomial order in the algebraic sense
    (compatible with multiplication, well-founded), but no proofs are required
    here — correctness of Buchberger's algorithm is on the formal side. -/
structure CMonomialOrder (σ : Type*) where
  /-- `lt a b` returns `true` when `a` is strictly less than `b`. -/
  lt : CMonomial σ → CMonomial σ → Bool

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]

/-- `ord.le a b` returns `true` when `a ≤ b`. -/
def le (ord : CMonomialOrder σ) (a b : CMonomial σ) : Bool :=
  ord.lt a b || a == b

/-- `ord.compare a b` returns the `Ordering` between `a` and `b`. -/
def compare (ord : CMonomialOrder σ) (a b : CMonomial σ) : Ordering :=
  if ord.lt a b then .lt
  else if a == b then .eq
  else .gt

/-- `ord.max a b` returns the larger of the two monomials. -/
def max (ord : CMonomialOrder σ) (a b : CMonomial σ) : CMonomial σ :=
  if ord.lt a b then b else a

-- ============================================================
-- Concrete orders
-- ============================================================

-- ---- Private comparison helpers on raw sorted-descending lists ----

-- Lex comparison on sorted-descending lists.
-- Returns the Ordering between `a` and `b` in lexicographic order.
private def lexCmpList [DecidableEq σ] [LinearOrder σ]
    (a b : List (σ × ℕ)) : Ordering :=
  match a, b with
  | [], []                         => .eq
  | [], (_, e) :: _                => if e > 0 then .lt else .eq
  | (_, e) :: _, []                => if e > 0 then .gt else .eq
  | (x, ex) :: as, (y, ey) :: bs  =>
    if x == y then
      if ex < ey then .lt
      else if ex > ey then .gt
      else lexCmpList as bs
    else if x > y then .gt   -- x appears in a (positive exp), not in b
    else .lt                  -- y appears in b (positive exp), not in a
termination_by a.length + b.length

-- Grevlex tiebreak on sorted-ascending (reversed) lists.
-- Compare from the smallest variable; SMALLER exponent = LARGER in grevlex.
private def grevlexAscCmp [DecidableEq σ] [LinearOrder σ]
    (a b : List (σ × ℕ)) : Ordering :=
  match a, b with
  | [], []                         => .eq
  | [], (_, e) :: _                => if e > 0 then .gt else .eq
  | (_, e) :: _, []                => if e > 0 then .lt else .eq
  | (x, ex) :: as, (y, ey) :: bs  =>
    if x == y then
      -- At same variable: smaller exponent is LARGER in grevlex
      if ex < ey then .gt
      else if ex > ey then .lt
      else grevlexAscCmp as bs
    else if x < y then
      -- x is the smallest unmatched; a has ex > 0, b has 0 at x → a < b
      .lt
    else
      -- y is the smallest unmatched; b has ey > 0, a has 0 at y → a > b
      .gt
termination_by a.length + b.length

-- ---- Public concrete orders ----

/-- Pure lexicographic order.

    `a <_lex b` iff at the largest variable `x` where `expOf x a ≠ expOf x b`,
    `expOf x a < expOf x b`. -/
def lex : CMonomialOrder σ where
  lt a b := lexCmpList a.toExps b.toExps == .lt

/-- Graded lexicographic order.

    Compare total degree first; break ties by `lex`. -/
def grlex : CMonomialOrder σ where
  lt a b :=
    let da := a.totalDeg; let db := b.totalDeg
    if da < db then true
    else if da > db then false
    else lexCmpList a.toExps b.toExps == .lt

/-- Graded reverse lexicographic order.

    Compare total degree first; break ties from the *smallest* variable,
    with a smaller exponent meaning a larger monomial. -/
def grevlex : CMonomialOrder σ where
  lt a b :=
    let da := a.totalDeg; let db := b.totalDeg
    if da < db then true
    else if da > db then false
    else grevlexAscCmp a.toExps.reverse b.toExps.reverse == .lt

end CMonomialOrder

-- ============================================================
-- Order-dependent operations on CMvPolynomial
-- ============================================================

namespace CMvPolynomial

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]
variable {R : Type*} [Field R] [DecidableEq R]

/-- The leading monomial of `p` with respect to `ord`, if `p ≠ 0`. -/
def leadMon (ord : CMonomialOrder σ) (p : CMvPolynomial σ R) : Option (CMonomial σ) :=
  p.toTerms.foldl (fun acc (m, _) =>
    match acc with
    | none      => some m
    | some best => if ord.lt best m then some m else some best
  ) none

/-- The leading coefficient of `p` with respect to `ord`, if `p ≠ 0`. -/
def leadCoeff (ord : CMonomialOrder σ) (p : CMvPolynomial σ R) : Option R :=
  (p.leadMon ord).bind fun m =>
    (p.toTerms.find? fun (n, _) => n == m) |>.map Prod.snd

/-- The leading term of `p` with respect to `ord` (as a polynomial), if `p ≠ 0`. -/
def leadTerm (ord : CMonomialOrder σ) (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  match p.leadMon ord, p.leadCoeff ord with
  | some m, some c => ofMon m c
  | _,      _      => zero

/-- Remove the leading term from `p` (with respect to `ord`). -/
def tail (ord : CMonomialOrder σ) (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  match p.leadMon ord with
  | none   => p
  | some m => CMvPolynomial.mk (p.toTerms.filter fun (n, _) => n != m)

end CMvPolynomial
