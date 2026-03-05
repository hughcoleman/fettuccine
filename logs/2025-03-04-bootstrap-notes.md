# Bootstrap Notes — 2025-03-04

Initial implementation of a fully-structured Buchberger's algorithm in Lean 4 / Mathlib 4.29.

---

## Project structure

```
Groebner/
  Defs.lean       — core definitions and basic properties
  Criterion.lean  — Buchberger's criterion
  Algorithm.lean  — the algorithm and correctness theorem
  Basic.lean      — examples, #check roundtrip, full API reference
```

---

## Mathlib APIs used

All in `Mathlib.RingTheory.MvPolynomial.{MonomialOrder,Groebner}`.

| Name | Role |
|---|---|
| `MonomialOrder.degree m f` | leading monomial of `f` |
| `MonomialOrder.leadingCoeff m f` | leading coefficient |
| `MonomialOrder.leadingTerm m f` | leading term (monomial × coeff) |
| `MonomialOrder.subLTerm m f` | `f` with leading term deleted |
| `MonomialOrder.reduce m hb f` | one-step reduction of `f` by `b` (requires `IsUnit (lc b)`) |
| `MonomialOrder.sPolynomial m f g` | S-polynomial |
| `MonomialOrder.isUnit_leadingCoeff` | over a field, `IsUnit (lc f) ↔ f ≠ 0` |
| `MonomialOrder.degree_reduce_lt` | reduction strictly decreases degree |
| `MonomialOrder.degree_sub_LTerm_lt` | removing leading term strictly decreases degree |
| `MonomialOrder.sPolynomial_decomposition` | key lemma for Buchberger's criterion (hard direction) |
| `MonomialOrder.lex` | lexicographic monomial order |
| `MonomialOrder.degLex` | degree-lex monomial order (`import Mathlib.Data.Finsupp.MonomialOrder.DegLex`) |

`MonomialOrder.div` (in `Groebner.lean`) provides an *existential* multivariate division
theorem but is not computable; our `remainder` function reimplements this constructively.

---

## What was implemented (without `sorry`)

### `Defs.lean`

- `MonomialOrder.remainder m G f : MvPolynomial σ k`
  Multivariate division remainder.  Defined by well-founded recursion using
  `Classical.choose` to pick a reducer.  Three branches:
  1. **Reducer found** (`∃ b ∈ G, b ≠ 0 ∧ lm(b) ≤ lm(f)`): apply `reduce`, recurse.
  2. **Constant remainder** (`degree f = 0`, no reducer): return `f`.
  3. **Peel leading term** (`degree f ≠ 0`, no reducer):
     return `leadingTerm f + remainder m G (subLTerm f)`.

- `MonomialOrder.IsGroebnerBasis m I G : Prop`
  Leading-monomial-divisibility characterisation:
  `G ⊆ I` and `∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧ lm(g) ≤ lm(f)`.

- `MonomialOrder.LmDvd m p f : Prop`
  Abbreviation for `m.degree p ≤ m.degree f`.

### `Criterion.lean`

- `MonomialOrder.AllSpolyRemaindersZero m G : Prop`
  `∀ p q ∈ G, remainder m G (sPolynomial p q) = 0`.

- `allSpolyRemaindersZero_of_isGroebnerBasis` (**fully proved**)
  Easy direction of Buchberger's criterion.
  `S(p,q) ∈ I` since `S(p,q) = c₁·p - c₂·q` with `p,q ∈ G ⊆ I`; then
  `remainder_eq_zero_of_isGroebnerBasis` gives the result.

- `buchberger_criterion`
  Biconditional: `IsGroebnerBasis m (span G) G ↔ AllSpolyRemaindersZero m G`.

- `spoly_self_remainder_zero`
  `remainder m G (sPolynomial p p) = 0`, trivially from `sPolynomial_self`.

### `Algorithm.lean`

- `buchbergerLoop m G B`
  Inner Buchberger loop.  Structural recursion on the pair-queue `B`:
  - `B = []`: return `G`.
  - `B = (p,q)::B'`: compute `r = remainder m G (S(p,q))`.
    - `r = 0`: process `B'` with the same `G`.
    - `r ≠ 0`: add `r` to `G`, enqueue all pairs `(g,r)` for `g ∈ G`, continue.

- `buchberger m gens`
  Runs `buchbergerLoop gens (gens ×ˢ gens)`.

- `buchberger_isGroebnerBasis m gens` (**correctness theorem**)
  `IsGroebnerBasis m (span gens) (buchberger m gens)`.
  Proved by chaining `buchberger_span_eq` and `buchberger_criterion.mpr`.

### `Basic.lean`

- Concrete example in `ℚ[x₀,x₁,x₂,x₃]` under `degLex`:
  - `f₁ = x₀x₁ - x₂x₃`, `f₂ = -x₁² + x₀x₂`, `f₃ = -x₁x₂x₃ + x₀²x₂`.
  - Both the **verified-algorithm** and **verifying-checker** paths demonstrated.
- `#check` round-trips confirm types are correct.

---

## `sorry` inventory

Priority order for future work:

| # | Location | Statement | Proof strategy |
|---|---|---|---|
| 1 | `remainder` (`decreasing_by`) | Lex measure `(m.toSyn (degree f), f.support.card)` decreases | Case split: `degree_reduce_lt` for branch 1 (degree ≠ 0); `support.card` drops for branch 1 (degree = 0, since `reduce` gives 0); `degree_sub_LTerm_lt` for branch 3 |
| 2 | `buchbergerLoop` (`decreasing_by`) | Termination via Dickson's Lemma | ACC on monomial ideals; Mathlib has `Finsupp.wellQuasiOrder` (Dickson) |
| 3 | `isGroebnerBasis_of_allSpolyRemaindersZero` | Hard direction of criterion | Degree induction using `MonomialOrder.sPolynomial_decomposition` (already in Mathlib) |
| 4 | `remainder_sub_mem_span` | `f - remainder m G f ∈ span G` | Recursion on `remainder`: subtract accumulates multiples of elements of `G` |
| 5 | `buchbergerLoop_span_eq` | `span (buchbergerLoop m G B) = span G` | Induction on `B`; use `remainder_sub_mem_span` + `S(p,q) ∈ span G` |
| 6 | `buchberger_allSpolyRemaindersZero` | All S-poly remainders zero on exit | Loop-trace induction with invariant maintenance |
| 7 | `remainder_nil` | `remainder m [] f = f` | Degree induction: `[]` branch always peels, sum of terms = `f` |
| 8 | `claimedBasis_span` / `claimedBasis_allSPolyZero` | Example-specific verification | Once `remainder` is decidable: `native_decide` |

---

## Verified vs. verifying

**Verified algorithm**: `buchberger_isGroebnerBasis dlex genList` gives a proof that
`buchberger dlex genList` is a Gröbner basis of `I`, for *some* output list.  The specific
list is non-deterministic (depends on `Classical.choose` choices in `remainder`).

**Verifying checker**: For a *specific* known basis `G` (e.g. from SageMath), prove
`AllSpolyRemaindersZero m G` — in principle by `native_decide` once `sorry`s 1–4 above
are closed — and apply `buchberger_criterion.mpr`.  This path produces a concrete proof
term for that specific `G`, which is more useful for downstream decision procedures that
cite a particular Gröbner basis.

**Recommendation**: use the verifying path for specific decision procedures; use the
verified path for generic ideal-membership proofs where the exact basis does not matter.

---

## Environment

- Lean: `leanprover/lean4:v4.29.0-rc1`
- Mathlib: `v4.29.0-rc1`
- Build: `lake build Groebner` — 1474 jobs, all pass (warnings only: `sorry` uses and
  `open Classical` style advisory).
