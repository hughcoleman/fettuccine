import Fettuccine.Algorithm.FMvPolynomial
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Logic.Equiv.Array

/-!
# "Fast" Monomial Orders

This file defines three standard monomial orders on `FMonomial`, given as comparison functions of
type `FMonomial n → FMonomial n → Ordering`.

## Definitions

* `FMonomialOrder.lex` - the lexicographic order on `FMonomial`.
* `FMonomialOrder.grlex` - the graded lexicographic order on `FMonomial`.
* `FMonomialOrder.grevlex` - the graded reverse lexicographic order on `FMonomial`.
-/

/-- A **monomial order** on `FMonomial n` is a total, translation-invariant well-founded binary
    relation. -/
abbrev FMonomialOrder (n : ℕ) := FMonomial n → FMonomial n → Ordering

namespace FMonomialOrder

/-- The lexicographic order on monomials. -/
def lex {n : ℕ} (m₁ m₂ : FMonomial n) : Ordering :=
  (List.range n).foldl (init := .eq) fun acc i =>
    match acc with
    | .eq => compare (m₁.toArray.getD i 0) (m₂.toArray.getD i 0)
    | o   => o

/-- The reverse lexicographic order on monomials. -/
-- One way to obtain the reverse lexicographic order is to reverse the underlying alphabet, apply
-- `lex`, and then reverse.
def revlex {n : ℕ} (m₁ m₂ : FMonomial n) : Ordering :=
  ((List.range n).reverse).foldl (init := .eq) fun acc i =>
    match acc with
    | .eq => compare (m₂.toArray.getD i 0) (m₁.toArray.getD i 0)
    | o   => o

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

private abbrev m (a b c : ℕ) : FMonomial 3 :=
  Vector.mk #[a, b, c] (by simp)

-- x >[lex] y
example : lex (m 1 0 0) (m 0 1 0) == .gt := by
  rfl
-- y² >[lex] yz
example : lex (m 0 2 0) (m 0 1 1) == .gt := by
  rfl
-- y <[grlex] x²
example : grlex (m 0 1 0) (m 2 0 0) == .lt := by
  rfl
-- xy <[grlex] x² (same degree, so fall back to lex)
example : grlex (m 1 1 0) (m 2 0 0) == .lt := by
  rfl
-- xz <[grevlex] y²
example : grevlex (m 1 0 1) (m 0 2 0) == .lt := by
  rfl

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

/-- The leading term of `f` is none if and only if `f` is the zero polynomial. -/
theorem leadingTerm_none_iff (ord : FMonomialOrder n) (f : FMvPolynomial n R) :
    f.leadingTerm ord = none ↔ f = #[] := by
  let step : Option (FMonomial n × R) → (FMonomial n × R) → Option (FMonomial n × R) :=
    fun lt (m, c) =>
      match lt with
      | none          => some (m, c)
      | some (m', c') =>
        if ord m m' == .gt then some (m, c) else some (m', c')
  -- Folding `step` with an non-none accumulator produces a non-none result.
  have hfold_some :
      ∀ (l : List (FMonomial n × R)) (lt : Option (FMonomial n × R)),
        lt ≠ none → List.foldl step lt l ≠ none := by
    intro l
    induction l with
    | nil => intro lt hlt; simpa [step]
    | cons a l ih =>
      intro lt hlt
      -- A single step doesn't produce a none result.
      have hstep : step lt a ≠ none := by
        cases lt with
        | none     => simp [step]
        | some val =>
          simp [step]; cases ord _ _ <;> simp
      exact ih _ hstep
  -- Express the leading term as a list-based fold, so that we can apply the previous theorems.
  unfold leadingTerm
  rw [← Array.foldl_toList]
  cases h : f.toList with
  | nil =>
    -- In this case, the goal reduces to `true ↔ true`, which is true.
    have hf : f = #[] :=
      (Equiv.arrayEquivList _).injective <| by simpa using h
    simp [hf]
  | cons a l =>
    have hf : f ≠ #[] := by
      intro hf
      simp [hf] at h
    have hsome : List.foldl step (some a) l ≠ none :=
      hfold_some l (some a) (by simp)
    -- We get a contradiction either way we look.
    constructor
    · intro hnone
      have hnone' : List.foldl step (some a) l = none := by
        simpa [step] using hnone
      contradiction
    · intro hf'
      exact (hf hf').elim

lemma leadingMonomial_none_iff (ord : FMonomialOrder n) (f : FMvPolynomial n R) :
    f.leadingMonomial ord = none ↔ f = #[] := by
  simp [leadingMonomial, leadingTerm_none_iff]

lemma leadingCoefficient_none_iff (ord : FMonomialOrder n) (f : FMvPolynomial n R) :
    f.leadingCoefficient ord = none ↔ f = #[] := by
  simp [leadingCoefficient, leadingTerm_none_iff]

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

lemma normalize_zero : normalize (n := n) (R := R) zero = zero := by
  rfl

/-- Add two multivariate polynomials. -/
def add (f g : FMvPolynomial n R) : FMvPolynomial n R :=
  normalize (f ++ g)

lemma add_zero (f : FMvPolynomial n R) :
    add f zero = normalize f := by
  simp [add, FMvPolynomial.zero]

lemma zero_add (f : FMvPolynomial n R) :
    add zero f = normalize f := by
  simp [add, FMvPolynomial.zero]

/-- Subtract a multivariate polynomial from another. -/
def sub [AddGroup R] (f g : FMvPolynomial n R) : FMvPolynomial n R :=
  add f (g.map fun (m, c) => (m, -c))

/-- Multiply a polynomial by a monomial term. -/
def mulMonomial [Mul R] (m : FMonomial n) (c : R)
    (f : FMvPolynomial n R) : FMvPolynomial n R :=
  normalize (f.map fun (m', c') => (FMonomial.add m m', c * c'))

/-- Multiply two multivariate polynomials. -/
def mul [Mul R] (f g : FMvPolynomial n R) : FMvPolynomial n R :=
  f.foldl (init := #[]) fun acc (m, c) => add acc (mulMonomial m c g)

lemma zero_mul [Mul R] (f : FMvPolynomial n R) :
    mul zero f = zero := by
  simp [mul, FMvPolynomial.zero]

end FMvPolynomial
