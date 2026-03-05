# Groebner — Project Overview

## Goal

This project provides **certifying computational algorithms in commutative algebra** in
Lean 4 / Mathlib.  The aim is not merely to compute algebraic invariants, but to produce
machine-checked proofs of correctness that compose with Mathlib theorems to prove
non-trivial facts about polynomial rings.

## Motivating Example: Proving an Ideal is Radical

Given an ideal `J ⊆ k[x₁, …, xₙ]` with explicit generators, prove `J` is radical:

1. **Compute** a Gröbner basis `G` for `J` using `buchbergerPoly` (fully computable).
2. **Certify** `G` is a Gröbner basis: `buchberger_criterion` reduces this to checking
   that all S-polynomial remainders vanish — a decidable condition closed by
   `native_decide` once the bridge (see below) exists.
3. **Apply theory**: e.g., "if the initial monomial ideal `in(J)` is squarefree, then `J`
   is radical."  The certified `G` gives `in(J) = ⟨lm(g) | g ∈ G⟩`, and squarefreeness
   of the leading monomials is checkable by inspection.

Other use cases (Cohen-Macaulay, primary decomposition, dimension, …) follow the same
pattern: compute a certificate, certify it, apply theory.

## Architecture

```
Groebner/
  Defs.lean      — remainder, IsGroebnerBasis  (noncomputable, MvPolynomial-based)
  Criterion.lean — AllSpolyRemaindersZero, buchberger_criterion  (noncomputable)
  Poly.lean      — buchbergerPoly, polyOf, fmtPoly  (fully computable, #eval-able)
  Basic.lean     — examples, API reference, sorry inventory
```

**Computable world** (`Poly.lean`): `Poly = List (List ℕ × ℚ)`.  All operations are
`def` or `partial def`; supports `#eval` and `native_decide`.

**Formal world** (`Defs.lean`, `Criterion.lean`): noncomputable `MvPolynomial`-based
definitions; supports theorem proving and composition with Mathlib.

## The Missing Bridge

The two worlds are currently disconnected.  The central missing piece is:

```lean
-- The canonical embedding of the computable type into MvPolynomial:
embed : Poly → MvPolynomial (Fin n) k

-- A computable Boolean checker (using remainderPoly):
allSpolyRemaindersZeroPoly : List Poly → Bool

-- The bridge theorem:
theorem allSpolyRemaindersZeroPoly_iff (m : MonomialOrder (Fin n)) (G : List Poly) :
    allSpolyRemaindersZeroPoly G = true ↔
    AllSpolyRemaindersZero m (G.map embed)
```

With this, certifying a concrete basis looks like:

```lean
-- Step 1: native_decide compiles and runs buchbergerPoly + the checker natively.
have hcheck : allSpolyRemaindersZeroPoly (buchbergerPoly gens) = true :=
  by native_decide
-- Step 2: The bridge promotes the Boolean fact to a formal proposition.
have hzero : AllSpolyRemaindersZero m ((buchbergerPoly gens).map embed) :=
  (allSpolyRemaindersZeroPoly_iff m _).mp hcheck
-- Step 3: Buchberger's criterion gives IsGroebnerBasis.
exact (buchberger_criterion m).mpr hzero
```

This is the primary next milestone.

## Sorry Inventory

Sorries blocking the formal side.  Priority order:

1. `remainder` termination (`Defs.lean`) — lex decrease on `(degree, support.card)`
2. Hard direction of `buchberger_criterion` (`Criterion.lean`) —
   `sPolynomial_decomposition` induction
3. `remainder_nil`, `remainder_sub_mem_span` (`Defs.lean`) — degree induction

These are needed for the formal proofs (e.g. step 3 above), but **not** for the
computable side (`buchbergerPoly`, `#eval`, `native_decide`).

## Implementation Notes

- `buchbergerPoly` uses `partial def` for `remainderPoly` and `buchbergerLoop`.
  These are permanently opaque to the kernel — the InfoView cannot reduce them.
  Use `#eval` for interactive display; use `native_decide` for proof-relevant checks.

- Coefficients are `ℚ` throughout `Poly.lean`.  The bridge theorem will likely need
  to be stated over `ℚ` first, with a possible generalisation to other fields later.

- The monomial ordering in `Poly.lean` is degree-lex, matching `MonomialOrder.degLex`
  for `Fin n` (degree first, then lex from the largest index down).

- `buchberger_criterion` is stated for any `MonomialOrder σ` over a `Field k`.
  Instantiating it at `σ = Fin n`, `k = ℚ`, `m = MonomialOrder.degLex` for the
  bridge is the expected path.
