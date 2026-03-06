import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.MvPolynomial.Groebner

/-!
# Computable Monomials and Multivariate Polynomials

This file defines two computable types:
- `CMonomial σ` — a monomial in variables of type `σ`
- `CMvPolynomial σ R` — a multivariate polynomial over a commutative semiring `R`

Both types are initially **reducible** (so all internal helpers can use list
operations directly) and then sealed as `@[irreducible]` at the end of the file,
making their `List`-based representation opaque to importing modules.

## Representation

* `CMonomial σ  = List (σ × ℕ)` — sorted **descending** by `σ`'s `LinearOrder`;
  all stored exponents are positive.
* `CMvPolynomial σ R = List (CMonomial σ × R)` — no duplicate monomials;
  no zero coefficients; terms stored in unspecified order.
  (Ordering is the responsibility of `CMonomialOrder`.)

## Bridge to Mathlib

* `CMonomial.toFinsupp : CMonomial σ → σ →₀ ℕ` lifts a monomial to a `Finsupp`.
* `CMvPolynomial.toMvPolynomial : CMvPolynomial σ R → MvPolynomial σ R` is the
  canonical ring map to Mathlib's `MvPolynomial`.
-/

-- ============================================================
-- CMonomial
-- ============================================================

/-- A computable monomial over variables drawn from `σ`.

    The internal representation is a list of `(variable, exponent)` pairs
    sorted in **descending** order by `σ`'s `LinearOrder`, with all
    exponents strictly positive.  Use the API; do not pattern-match directly. -/
abbrev CMonomial (σ : Type*) := List (σ × ℕ)

namespace CMonomial

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]

-- ----------------------------------------
-- Private list-level primitives
-- ----------------------------------------

/-- Merge two sorted-descending `(variable, exponent)` lists, **summing** exponents
    for variables that appear in both.  Entries with sum 0 are dropped. -/
private def mergeAdd (a b : List (σ × ℕ)) : List (σ × ℕ) :=
  match a, b with
  | [], _  => b
  | _,  [] => a
  | (x, ex) :: as, (y, ey) :: bs =>
    if x == y then
      let s := ex + ey
      if s == 0 then mergeAdd as bs else (x, s) :: mergeAdd as bs
    else if x > y then (x, ex) :: mergeAdd as ((y, ey) :: bs)
    else                (y, ey) :: mergeAdd ((x, ex) :: as) bs
termination_by a.length + b.length

/-- Merge two sorted-descending lists, taking the **maximum** exponent for each
    variable (i.e. the exponent of their LCM). -/
private def mergeLcm (a b : List (σ × ℕ)) : List (σ × ℕ) :=
  match a, b with
  | [], _  => b
  | _,  [] => a
  | (x, ex) :: as, (y, ey) :: bs =>
    if x == y then (x, max ex ey) :: mergeLcm as bs
    else if x > y then (x, ex) :: mergeLcm as ((y, ey) :: bs)
    else                (y, ey) :: mergeLcm ((x, ex) :: as) bs
termination_by a.length + b.length

/-- Check whether sorted-descending list `a` divides `b` componentwise. -/
private def dvdList (a b : List (σ × ℕ)) : Bool :=
  match a, b with
  | [],     _  => true
  | _ :: _, [] => false   -- a has a variable not in b
  | (x, ex) :: as, (y, ey) :: bs =>
    if x == y then ex ≤ ey && dvdList as bs
    else if x > y then false    -- x is in a but not in b
    else dvdList ((x, ex) :: as) bs   -- y is in b but not a; skip it
termination_by a.length + b.length

/-- `tdivList b a` computes `b / a` (exponent-wise `b - a`), assuming `a | b`.
    Both lists are sorted descending. -/
private def tdivList (b a : List (σ × ℕ)) : List (σ × ℕ) :=
  match b, a with
  | _,  []          => b        -- divide by 1
  | [], _ :: _      => []       -- shouldn't occur if a | b
  | (x, ex) :: bs, (y, ey) :: as =>
    if x == y then
      let diff := ex - ey
      let rest := tdivList bs as
      if diff == 0 then rest else (x, diff) :: rest
    else if x > y then
      (x, ex) :: tdivList bs ((y, ey) :: as)
    else
      tdivList ((x, ex) :: bs) as   -- defensive
termination_by b.length + a.length

/-- Normalise a raw exponent list into canonical form. -/
private def normalizeList (exps : List (σ × ℕ)) : List (σ × ℕ) :=
  exps.foldl (fun acc (x, e) =>
    if e == 0 then acc else mergeAdd acc [(x, e)]
  ) []

/-- Format a raw exponent list as a human-readable string. -/
private def fmtList [Repr σ] (exps : List (σ × ℕ)) : String :=
  if exps.isEmpty then "1"
  else
    (exps.map fun (x, e) =>
      let xs := (Repr.reprPrec x 0).pretty
      if e == 1 then xs else s!"{xs}^{e}")
    |> String.intercalate " * "

-- ----------------------------------------
-- Public API
-- ----------------------------------------

/-- The trivial monomial (the empty product `1`). -/
def one : CMonomial σ := []

/-- The monomial consisting of a single variable `x` raised to the first power. -/
def ofVar (x : σ) : CMonomial σ := [(x, 1)]

/-- Construct a `CMonomial` from an arbitrary list of `(variable, exponent)` pairs.
    Entries with the same variable are merged; zero exponents are dropped;
    the result is sorted in descending order by variable. -/
def mk (exps : List (σ × ℕ)) : CMonomial σ := normalizeList exps

/-- Extract the internal `(variable, exponent)` list (descending). -/
def toExps (m : CMonomial σ) : List (σ × ℕ) := m

/-- Total degree: the sum of all exponents. -/
def totalDeg (m : CMonomial σ) : ℕ := (m : List (σ × ℕ)).foldl (fun acc (_, e) => acc + e) 0

/-- Exponent of variable `x` in `m` (returns 0 if `x` does not appear). -/
def expOf (x : σ) (m : CMonomial σ) : ℕ :=
  ((m : List (σ × ℕ)).find? fun (y, _) => y == x).map Prod.snd |>.getD 0

/-- Product of two monomials (add exponents). -/
def mul (a b : CMonomial σ) : CMonomial σ := mergeAdd a b

/-- LCM of two monomials (take the maximum exponent for each variable). -/
def lcm (a b : CMonomial σ) : CMonomial σ := mergeLcm a b

/-- `a.dvd b` is `true` iff monomial `a` divides monomial `b`. -/
def dvd (a b : CMonomial σ) : Bool := dvdList a b

/-- Exact division `b.tdiv a`, assuming `a.dvd b = true`.
    Returns the monomial `c` such that `c * a = b`. -/
def tdiv (b a : CMonomial σ) : CMonomial σ := tdivList b a

/-- Typeclass instances. -/
instance : Mul (CMonomial σ)  := ⟨mul⟩
instance : One (CMonomial σ)  := ⟨one⟩

/-- Human-readable formatted monomial. -/
def fmt [Repr σ] (m : CMonomial σ) : String := fmtList m

instance [Repr σ] : Repr (CMonomial σ) where
  reprPrec m _ := Std.Format.text (fmtList m)

instance [Repr σ] : ToString (CMonomial σ) := ⟨fmt⟩

end CMonomial

-- Equality/BEq instances for CMonomial: only [DecidableEq σ] required,
-- not [LinearOrder σ], so they can be found wherever CMonomial is used.
section CMonomial_EqInstances
variable {σ : Type*} [DecidableEq σ]
instance CMonomial.instDecidableEqCMonomial : DecidableEq (CMonomial σ) := inferInstance
instance CMonomial.instBEqCMonomial : BEq (CMonomial σ) := ⟨fun a b => decide (a = b)⟩
end CMonomial_EqInstances

-- ============================================================
-- CMvPolynomial
-- ============================================================

/-- A computable multivariate polynomial over a commutative semiring `R` in variables `σ`.

    Internally a list of `(CMonomial σ, R)` pairs with no duplicate monomials
    and no zero coefficients.  The terms are stored in unspecified order;
    use the order-dependent API in `CMonomialOrder` for leading-term operations. -/
abbrev CMvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] := List (CMonomial σ × R)

namespace CMvPolynomial

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]
variable {R : Type*} [CommRing R] [DecidableEq R]

-- ----------------------------------------
-- Private normalisation helper
-- ----------------------------------------

/-- Combine duplicate monomials and drop zero terms. -/
private def normTerms (terms : List (CMonomial σ × R)) : CMvPolynomial σ R :=
  terms.foldl (fun acc (m, c) =>
    let (same, rest) := (acc : List (CMonomial σ × R)).partition fun (n, _) => n == m
    let c' := same.foldl (fun s (_, d) => s + d) c
    if c' == 0 then rest else rest ++ [(m, c')]
  ) []

/-- Format a term list as a human-readable string. -/
private def fmtTerms [Repr σ] [Repr R] (terms : CMvPolynomial σ R) : String :=
  if (terms : List (CMonomial σ × R)).isEmpty then "0"
  else
    ((terms : List (CMonomial σ × R)).map fun (m, c) =>
      let cs := (Repr.reprPrec c 0).pretty
      if m == CMonomial.one then cs
      else s!"{cs} * {CMonomial.fmt m}")
    |> String.intercalate " + "

-- ----------------------------------------
-- Public API
-- ----------------------------------------

/-- The zero polynomial. -/
def zero : CMvPolynomial σ R := []

/-- The constant polynomial `1`. -/
def one : CMvPolynomial σ R := [(CMonomial.one, 1)]

/-- The constant polynomial `c`. -/
def ofConst (c : R) : CMvPolynomial σ R :=
  if c == 0 then [] else [(CMonomial.one, c)]

/-- A single term `c * m`. -/
def ofMon (m : CMonomial σ) (c : R) : CMvPolynomial σ R :=
  if c == 0 then [] else [(m, c)]

/-- The linear polynomial corresponding to a single variable `x`. -/
def ofVar (x : σ) : CMvPolynomial σ R := [(CMonomial.ofVar x, 1)]

/-- Construct from an arbitrary list of `(monomial, coeff)` pairs. -/
def mk (terms : List (CMonomial σ × R)) : CMvPolynomial σ R := normTerms terms

/-- Extract the internal term list. -/
def toTerms (p : CMvPolynomial σ R) : List (CMonomial σ × R) := p

-- ----------------------------------------
-- Arithmetic
-- ----------------------------------------

/-- Addition. -/
def add (p q : CMvPolynomial σ R) : CMvPolynomial σ R :=
  normTerms ((p : List (CMonomial σ × R)) ++ q)

/-- Negation. -/
def neg (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  (p : List (CMonomial σ × R)).map fun (m, c) => (m, -c)

/-- Subtraction. -/
def sub (p q : CMvPolynomial σ R) : CMvPolynomial σ R :=
  add p (neg q)

/-- Scalar multiplication by a ring element `c`. -/
def smul (c : R) (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  if c == 0 then zero
  else (p : List (CMonomial σ × R)).map fun (m, d) => (m, c * d)

/-- Multiply every term by the monomial `shift`. -/
def monomialMul (shift : CMonomial σ) (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  (p : List (CMonomial σ × R)).map fun (m, c) => (CMonomial.mul shift m, c)

/-- Polynomial multiplication. -/
def mul (p q : CMvPolynomial σ R) : CMvPolynomial σ R :=
  normTerms ((p : List (CMonomial σ × R)).flatMap fun (m, c) =>
    (q : List (CMonomial σ × R)).map fun (n, d) => (CMonomial.mul m n, c * d))

-- ----------------------------------------
-- Instances
-- ----------------------------------------

instance : Add  (CMvPolynomial σ R) := ⟨add⟩
instance : Neg  (CMvPolynomial σ R) := ⟨neg⟩
instance : Sub  (CMvPolynomial σ R) := ⟨sub⟩
instance : Mul  (CMvPolynomial σ R) := ⟨mul⟩
instance : Zero (CMvPolynomial σ R) := ⟨zero⟩
instance : One  (CMvPolynomial σ R) := ⟨one⟩

/-- Allow `c * p` where `c : R` and `p : CMvPolynomial σ R`. -/
instance : HMul R (CMvPolynomial σ R) (CMvPolynomial σ R) := ⟨smul⟩

instance instDecidableEqCMvPolynomial : DecidableEq (CMvPolynomial σ R) := inferInstance

/-- Boolean equality for polynomials (derived from `DecidableEq`). -/
instance instBEqCMvPolynomial : BEq (CMvPolynomial σ R) := ⟨fun p q => decide (p = q)⟩

-- ----------------------------------------
-- Pretty-printing
-- ----------------------------------------

/-- Format a polynomial using `Repr σ` and `Repr R` for variable/coefficient names. -/
def fmt [Repr σ] [Repr R] (p : CMvPolynomial σ R) : String := fmtTerms p

instance [Repr σ] [Repr R] : Repr (CMvPolynomial σ R) where
  reprPrec p _ := Std.Format.text (fmtTerms p)

instance [Repr σ] [Repr R] : ToString (CMvPolynomial σ R) := ⟨fmt⟩

/-- Format a polynomial using explicit variable names.

    The function `varName : σ → String` assigns a display name to each variable.
    Example: `CMvPolynomial.fmtPoly (fun i => #["x₀","x₁","x₂"][i]!) p` -/
def fmtPoly [Repr R] (varName : σ → String) (p : CMvPolynomial σ R) : String :=
  if (p : List (CMonomial σ × R)).isEmpty then "0"
  else
    ((p : List (CMonomial σ × R)).map fun (m, c) =>
      let cs := (Repr.reprPrec c 0).pretty
      let ms := (m : List (σ × ℕ))
      if ms.isEmpty then cs
      else
        let mStr := (ms.map fun (x, e) =>
          if e == 1 then varName x else s!"{varName x}^{e}")
          |> String.intercalate " * "
        s!"{cs} * {mStr}")
    |> String.intercalate " + "

end CMvPolynomial

-- ============================================================
-- Bridge: CMonomial.toFinsupp and CMvPolynomial.toMvPolynomial
-- ============================================================

/-!
## Bridge to Mathlib's `MvPolynomial`

### `CMonomial.toFinsupp`

`toFinsupp` maps a `CMonomial σ` (a sorted list of `(variable, exponent)` pairs)
to `σ →₀ ℕ` by summing `Finsupp.single x e` over the variable–exponent list.
The canonical representation guarantees each variable appears at most once, so
`(toFinsupp m) x = m.expOf x` for every `x`.

### `CMvPolynomial.toMvPolynomial`

`toMvPolynomial` maps each `(m, c)` term to `MvPolynomial.monomial (toFinsupp m) c`
and sums over the term list.  This is a ring homomorphism (modulo the sorried lemmas).

### Sorry inventory

* `CMonomial.toFinsupp_expOf`          — sum-over-disjoint-singletons.
* `CMonomial.toFinsupp_injective`       — follows from `toFinsupp_expOf`.
* `CMonomial.toFinsupp_mul`             — exponent-addition after `mergeAdd`.
* `CMvPolynomial.toMvPolynomial_add`    — normTerms transparency.
* `CMvPolynomial.toMvPolynomial_neg`    — list-map over negation.
* `CMvPolynomial.toMvPolynomial_smul`   — scalar multiplication linearity.
* `CMvPolynomial.toMvPolynomial_monomialMul` — monomial-shift commutation.
-/

open MvPolynomial

-- ----------------------------------------
-- CMonomial.toFinsupp
-- ----------------------------------------

namespace CMonomial

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]

/-- Lift a `CMonomial` to a `Finsupp` by summing `Finsupp.single x e` over all
`(x, e)` pairs.  The canonical representation guarantees each variable appears
at most once, so `(toFinsupp m) x = m.expOf x`. -/
noncomputable def toFinsupp (m : CMonomial σ) : σ →₀ ℕ :=
  ((m.toExps : List (σ × ℕ)).map fun (x, e) => Finsupp.single x e).sum

/-- `toFinsupp 1 = 0`. -/
@[simp]
lemma toFinsupp_one : toFinsupp (one (σ := σ)) = 0 := by
  simp [toFinsupp, one, toExps]

/-- `(toFinsupp m) x = m.expOf x`. -/
lemma toFinsupp_expOf (m : CMonomial σ) (x : σ) :
    toFinsupp m x = m.expOf x := by
  sorry

/-- `toFinsupp` is injective. -/
lemma toFinsupp_injective : Function.Injective (toFinsupp (σ := σ)) := by
  intro a b hab
  sorry

/-- `toFinsupp` respects multiplication: `toFinsupp (a * b) = toFinsupp a + toFinsupp b`. -/
lemma toFinsupp_mul (a b : CMonomial σ) :
    toFinsupp (a * b) = toFinsupp a + toFinsupp b := by
  ext x
  simp only [Finsupp.add_apply, toFinsupp_expOf]
  sorry

end CMonomial

-- ----------------------------------------
-- CMvPolynomial.toMvPolynomial
-- ----------------------------------------

namespace CMvPolynomial

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]
variable {R : Type*} [CommRing R] [DecidableEq R]

/-- Lift a `CMvPolynomial` to `MvPolynomial σ R` by mapping each term `(m, c)` to
`MvPolynomial.monomial (toFinsupp m) c` and summing. -/
noncomputable def toMvPolynomial (p : CMvPolynomial σ R) : MvPolynomial σ R :=
  ((p.toTerms : List (CMonomial σ × R)).map fun (m, c) =>
    MvPolynomial.monomial (CMonomial.toFinsupp m) c).sum

@[simp]
lemma toMvPolynomial_zero : toMvPolynomial (0 : CMvPolynomial σ R) = 0 := rfl

/-- `toMvPolynomial (ofMon m c) = monomial (toFinsupp m) c` when `c ≠ 0`. -/
lemma toMvPolynomial_ofMon (m : CMonomial σ) (c : R) (hc : c ≠ 0) :
    toMvPolynomial (ofMon m c) = MvPolynomial.monomial (CMonomial.toFinsupp m) c := by
  simp [toMvPolynomial, ofMon, toTerms, hc]

/-- `toMvPolynomial p = 0 ↔ p = 0`. -/
lemma toMvPolynomial_eq_zero_iff (p : CMvPolynomial σ R) :
    toMvPolynomial p = 0 ↔ p = 0 := by
  sorry

/-- `toMvPolynomial` is additive. -/
lemma toMvPolynomial_add (p q : CMvPolynomial σ R) :
    toMvPolynomial (p + q) = toMvPolynomial p + toMvPolynomial q := by
  sorry

/-- `toMvPolynomial` commutes with negation. -/
lemma toMvPolynomial_neg (p : CMvPolynomial σ R) :
    toMvPolynomial (-p) = -toMvPolynomial p := by
  simp only [toMvPolynomial, neg, toTerms, List.map_map]
  sorry

/-- `toMvPolynomial` commutes with subtraction. -/
@[simp]
lemma toMvPolynomial_sub (p q : CMvPolynomial σ R) :
    toMvPolynomial (p - q) = toMvPolynomial p - toMvPolynomial q := by
  have : p - q = p + (-q) := rfl
  rw [this, toMvPolynomial_add, toMvPolynomial_neg]; ring

/-- `toMvPolynomial` commutes with scalar multiplication. -/
lemma toMvPolynomial_smul (c : R) (p : CMvPolynomial σ R) :
    toMvPolynomial (smul c p) = c • toMvPolynomial p := by
  sorry

/-- `toMvPolynomial` commutes with monomial-shift multiplication. -/
lemma toMvPolynomial_monomialMul (shift : CMonomial σ) (p : CMvPolynomial σ R) :
    toMvPolynomial (monomialMul shift p) =
    MvPolynomial.monomial (CMonomial.toFinsupp shift) 1 * toMvPolynomial p := by
  sorry

end CMvPolynomial
