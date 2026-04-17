import Fettuccine.Algorithm.CMvPolynomial

/-!
# Computable Monomial Orders

This file defines three standard monomial orders on `CMonomial`, given as comparison functions of
type `CMonomial n → CMonomial n → Ordering`.

## Definitions

* `CMonomialOrder.lex` - the lexicographic order on `CMonomial`.
* `CMonomialOrder.grlex` - the graded lexicographic order on `CMonomial`.
* `CMonomialOrder.grevlex` - the graded reverse lexicographic order on `CMonomial`.
-/

namespace CMonomialOrder

/-- The lexicographic order on monomials. -/
def lex {n : ℕ} (m₁ m₂ : CMonomial n) : Ordering :=
  Id.run do
    for i in (List.range n) do
      let (a, b) := (m₁.data.getD i 0, m₂.data.getD i 0)
      if a < b then return .lt
      if a > b then return .gt
    return .eq

/-- The reverse lexicographic order on monomials. -/
private def revlex {n : ℕ} (m₁ m₂ : CMonomial n) : Ordering :=
  Id.run do
    for i in (List.range n).reverse do
      let (a, b) := (m₁.data.getD i 0, m₂.data.getD i 0)
      if a < b then return .gt
      if a > b then return .lt
    return .eq

/-- The graded lexicographic order on monomials. -/
def grlex {n : ℕ} (m₁ m₂ : CMonomial n) : Ordering :=
  match compare m₁.degree m₂.degree with
  | .eq => lex m₁ m₂
  | o   => o

/-- The graded reverse lexicographic order on monomials. -/
def grevlex {n : ℕ} (m₁ m₂ : CMonomial n) : Ordering :=
  match compare m₁.degree m₂.degree with
  | .eq => revlex m₁ m₂
  | o   => o

end CMonomialOrder

namespace CMvPolynomial

variable {n : ℕ}
variable {R : Type*}

/-- The leading term of a polynomial, if it exists. -/
def leadingTerm (f : CMvPolynomial n R) : Option (CMonomial n × R) :=
  -- Since we're storing the terms of the polynomial in decreasing order with respect to the
  -- implicit order, the leading term is just the first entry (if it exists).
  f[0]?

/-- The leading monomial of a polynomial, if it exists. -/
def leadingMonomial (f : CMvPolynomial n R) : Option (CMonomial n) :=
  f.leadingTerm.map Prod.fst

/-- The leading coefficient of a polynomial, if it exists. -/
def leadingCoefficient (f : CMvPolynomial n R) : Option R :=
  f.leadingTerm.map Prod.snd

variable [DecidableEq R] [Zero R] [AddMonoid R]
variable (ord : CMonomial n → CMonomial n → Ordering)

/-- Normalize a polynomial with respect to a given monomial order. -/
def normalize (f : CMvPolynomial n R) : CMvPolynomial n R :=
  merge (f.qsort fun (m₁, _) (m₂, _) => ord m₁ m₂ == .gt)
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

/-- Add two multivariate polynomials. -/
def add (f g : CMvPolynomial n R) : CMvPolynomial n R :=
  -- FIXME: This could be optimized by zipper-merging the two sorted arrays instead of concatenating
  --   and renormalizing.
  normalize ord (f ++ g)

/-- Subtract a multivariate polynomial from another. -/
def sub [AddGroup R] (f g : CMvPolynomial n R) : CMvPolynomial n R :=
  add ord f (g.map fun (m, c) => (m, -c))

/-- Multiply a multivariate polynomial by a monomial. -/
def mulMonomial [Mul R] (m : CMonomial n) (c : R) (f : CMvPolynomial n R) : CMvPolynomial n R :=
  normalize ord (f.map fun (m', c') => (CMonomial.add m m', c * c'))

end CMvPolynomial
