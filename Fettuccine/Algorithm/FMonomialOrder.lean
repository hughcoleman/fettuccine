import Fettuccine.Algorithm.FMvPolynomial
import Mathlib.Algebra.Field.Rat

/-!
# Fast Monomial Orders

This file defines three standard monomial orders on `FMonomial`, given as comparison functions of
type `FMonomial n → FMonomial n → Ordering`.

## Definitions

* `FMonomialOrder.lex` - the lexicographic order on `FMonomial`.
* `FMonomialOrder.grlex` - the graded lexicographic order on `FMonomial`.
* `FMonomialOrder.grevlex` - the graded reverse lexicographic order on `FMonomial`.
-/

abbrev FMonomialOrder (n : ℕ) := FMonomial n → FMonomial n → Ordering

namespace FMonomialOrder

/-- The lexicographic order on monomials. -/
def lex {n : ℕ} (m₁ m₂ : FMonomial n) : Ordering :=
  Id.run do
    for i in (List.range n) do
      let (a, b) := (m₁.data.getD i 0, m₂.data.getD i 0)
      if a < b then
        return .lt
      if a > b then
        return .gt
    return .eq

/-- The reverse lexicographic order on monomials. -/
-- One way to obtain the reverse lexicographic order is to reverse the underlying alphabet, apply
-- `lex`, and then reverse.
def revlex {n : ℕ} (m₁ m₂ : FMonomial n) : Ordering :=
  Id.run do
    for i in (List.range n).reverse do
      let (a, b) := (m₁.data.getD i 0, m₂.data.getD i 0)
      if a < b then
        return .gt
      if a > b then
        return .lt
    return .eq

/-- The graded lexicographic order on monomials. -/
def grlex {n : ℕ} (m₁ m₂ : FMonomial n) : Ordering :=
  match compare m₁.degree m₂.degree with
  | .eq => lex m₁ m₂
  | o   => o

/-- The graded reverse lexicographic order on monomials. -/
def grevlex {n : ℕ} (m₁ m₂ : FMonomial n) : Ordering :=
  match compare m₁.degree m₂.degree with
  | .eq => revlex m₁ m₂
  | o   => o

section Examples

private abbrev S := FMvPolynomial 3 ℚ

-- A small helper for generating monomials.
private def m (a b c : ℕ) : FMonomial 3 :=
  { data := #[a, b, c], hsize := by simp }

#eval lex (m 1 0 0) (m 0 1 0)  -- .gt  (x > y)
#eval lex (m 0 2 0) (m 0 1 1)  -- .gt  (y² > yz)

#eval grlex (m 0 1 0) (m 2 0 0)  -- .lt (y < x²: lower degree)
#eval grlex (m 1 1 0) (m 2 0 0)  -- .lt (xy < x²: same degree, lex)

#eval grevlex (m 1 0 0) (m 0 0 1)  -- .gt (x > z under grevlex)
#eval grevlex (m 2 0 0) (m 0 2 0)  -- .gt (x² > y² under grevlex)

end Examples

end FMonomialOrder

namespace FMvPolynomial

variable {n : ℕ}
variable {R : Type*}

section LeadingMonomial

variable (f : FMvPolynomial n R)

/-- The leading term of `f` with respect to a monomial order `ord`, if it exists. -/
def leadingTerm (ord : FMonomialOrder n) : Option (FMonomial n × R) :=
  -- WARNING: This relies on the fact that there are no duplicate or otherwise redundant terms in
  -- the expression of `f`.
  f.foldl (init := none) fun lt (m, c) =>
    match lt with
    | none          => some (m, c)
    | some (m', c') =>
      if ord m m' == .gt then some (m, c) else some (m', c')

/-- The leading monomial of `f` with respect to `ord`, if it exists. -/
def leadingMonomial (ord : FMonomialOrder n) : Option (FMonomial n) :=
  (f.leadingTerm ord).map Prod.fst

/-- The leading coefficient of `f` with respect to `ord`, if it exists. -/
def leadingCoefficient (ord : FMonomialOrder n) : Option R :=
  (f.leadingTerm ord).map Prod.snd

end LeadingMonomial

variable [DecidableEq R] [Zero R] [AddMonoid R]

/-- Normalize a polynomial with respect to lexicographic order. -/
def normalize (f : FMvPolynomial n R) : FMvPolynomial n R :=
  merge (f.qsort fun (m₁, _) (m₂, _) => FMonomialOrder.lex m₁ m₂ == .gt)
where
  merge f := f.foldl (init := #[]) fun acc (m, c) =>
    match acc.back? with
    | some (m', c') =>
      if m = m' then
        let c₀ := c' + c
        if c₀ = (0 : R) then acc.pop
        else
          acc.set! (acc.size - 1) (m', c₀)
      else
        if c = (0 : R) then acc
        else
          acc.push (m, c)
    | none =>
      if c = (0 : R) then acc
      else
        acc.push (m, c)

/-- Add two multivariate polynomials and re-normalize lexicographically. -/
def add (f g : FMvPolynomial n R) : FMvPolynomial n R :=
  normalize (f ++ g)

/-- Subtract a multivariate polynomial from another. -/
def sub [AddGroup R] (f g : FMvPolynomial n R) : FMvPolynomial n R :=
  add f (g.map fun (m, c) => (m, -c))

/-- Multiply a polynomial by a monomial term and re-normalize lexicographically. -/
def mulMonomial [Mul R] (m : FMonomial n) (c : R)
    (f : FMvPolynomial n R) : FMvPolynomial n R :=
  normalize (f.map fun (m', c') => (FMonomial.add m m', c * c'))

/-- Multiply two multivariate polynomials and re-normalize lexicographically. -/
def mul [Mul R] (f g : FMvPolynomial n R) : FMvPolynomial n R :=
  f.foldl (init := #[]) fun acc (m, c) => add acc (mulMonomial m c g)

/-- Equality after lexicographic normalization. -/
def equal? (f g : FMvPolynomial n R) : Prop :=
  normalize f = normalize g

/-- Embed a numeric literal `k` as the constant polynomial `C k`. -/
instance instOfNat {k : ℕ} [OfNat R k] :
    OfNat (FMvPolynomial n R) k :=
  ⟨C (OfNat.ofNat k)⟩

end FMvPolynomial
