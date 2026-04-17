# Fettuccine: Large-Scale Implementation Plan

## Current State

The project is in excellent shape structurally. All core machinery is complete and proven:

- `CMvPolynomial.lean`: `CMonomial σ = Π₀ _ : σ, ℕ` and `CMvPolynomial σ R = ⨁ _ : CMonomial σ, R`
  — computable, all lemmas proven.
- `CMonomialOrder.lean`: abstract order structure + lex; grlex/grevlex in subdirectories
  — all fully proven.
- `Divide.lean`: full division algorithm, proven correct and unique.
- `Buchberger.lean`: algorithm runs, but `buchberger` theorem (line 84) is `sorry`.
- `Tactic.lean`: scaffold only — produces `sorry` for `IsGroebnerBasis₁`.

**The two gaps:** (a) Buchberger's criterion is unproven; (b) the tactic is a scaffold.

**The computability problem:** `DFinsupp`/`DirectSum` representations are mathematically
ideal but suffer from segfaults under `#eval` for grlex/grevlex. The root cause is that
`Finset.sup` traversal and the `ord.toSyn` round-trip are expensive/brittle under kernel
evaluation.

---

## Architectural Strategy

Two parallel layers:

```
┌──────────────────────────────────────────────────────┐
│  ALGORITHM LAYER (computation)                       │
│  FMonomial = Array ℕ                                 │
│  FMvPolynomial R = Array (FMonomial × R)             │
│  Fast orders, divide, buchberger                     │
└─────────────────────┬────────────────────────────────┘
                      │ translate + verify
┌─────────────────────▼────────────────────────────────┐
│  FORMAL LAYER (existing)                             │
│  CMvPolynomial, CMonomialOrder, mvDivide             │
│  IsGroebnerBasis₁ (decidable check)                  │
│  IsGroebnerBasis (mathematical, needs theorem)       │
└──────────────────────────────────────────────────────┘
```

**Critical insight:** `IsGroebnerBasis₁` (all S-polynomials reduce to 0) is **decidable**
for concrete coefficient rings like `ℚ` or `ZMod p`. So for concrete tactic goals, we can
verify the algorithm's output using `native_decide` without needing to prove
Buchberger's criterion. The mathematical theorem (`buchberger`) is then a separate,
independent development.

---

## Phase 1: `FMonomial` and `FMvPolynomial` ✅

**File:** `Fettuccine/Algorithm/MvPolynomial.lean`

```lean
abbrev FMonomial := Array ℕ
-- m[i] = exponent of variable i
-- All operations assume equal-length arrays (= number of variables n)
```

Operations implemented (all O(n) Array operations, no `Decidable` instances needed):

```lean
namespace FMonomial
def zero (n : ℕ) : FMonomial := Array.replicate n 0
def add  (m₁ m₂ : FMonomial) : FMonomial := Array.zipWith (· + ·) m₁ m₂
def degree (m : FMonomial) : ℕ := m.foldl (· + ·) 0
def lcm  (m₁ m₂ : FMonomial) : FMonomial := Array.zipWith max m₁ m₂
def divides (m₂ m₁ : FMonomial) : Bool :=   -- does m₂ divide m₁?
  (m₂.zip m₁).all fun (a, b) => Nat.ble a b
def divide (m₁ m₂ : FMonomial) : Option FMonomial :=
  if divides m₂ m₁ then some (Array.zipWith (· - ·) m₁ m₂) else none
end FMonomial
```

```lean
-- Sorted in DECREASING monomial order; no duplicate monomials; no zero coefficients.
abbrev FMvPolynomial (R : Type*) := Array (FMonomial × R)
```

Key operations in `namespace FMvPolynomial`:
- `leadingMonomial?`, `leadingCoefficient?` — O(1)
- `normalize ord` — sort, combine duplicates, drop zeros
- `add`, `sub`, `mulTerm` — merge-based arithmetic

---

## Phase 2: Monomial Orders ✅

**File:** `Fettuccine/Algorithm/MonomialOrder.lean`

Three comparison functions for `FMonomial` (all O(n), returning `Ordering`):

```lean
namespace FMonomialOrder
def lex     : FMonomial → FMonomial → Ordering  -- index 0 = highest priority
def grlex   : FMonomial → FMonomial → Ordering  -- degree first, then lex
def grevlex : FMonomial → FMonomial → Ordering  -- degree first, then reverse lex
end FMonomialOrder
```

No proof obligations in this phase — purely definitional. Proofs of
transitivity/well-foundedness for the formal connection come in Phase 5.

---

## Phase 3: Division ✅

**File:** `Fettuccine/Algorithm/Divide.lean`

```lean
-- Divide f by each gᵢ in gs in turn, returning (quotients, remainder).
-- Fuel-bounded; no termination proof needed.
def FMvPolynomial.divide (ord : FMonomial → FMonomial → Ordering)
    (f : FMvPolynomial R)
    (gs : Array (FMvPolynomial R))
    (fuel : ℕ := 4096)
    : Array (FMvPolynomial R) × FMvPolynomial R
```

Algorithm:
1. If `f = ∅` or `fuel = 0`, return `(quotients, accumulated_remainder)`.
2. Find first `gᵢ` with `in(gᵢ) | in(f)`.
3. If found: subtract the appropriate scaled multiple; recurse on the difference.
4. If not found: move `leadingTerm(f)` to remainder; recurse on `f - leadingTerm(f)`.

No correctness proof here — verified downstream via translation.

---

## Phase 4: Buchberger's Algorithm ✅

**File:** `Fettuccine/Algorithm/Buchberger.lean`

```lean
def FMvPolynomial.sPolynomial (ord : FMonomial → FMonomial → Ordering)
    (f g : FMvPolynomial R) : FMvPolynomial R

def FMvPolynomial.buchberger (ord : FMonomial → FMonomial → Ordering)
    (gens : Array (FMvPolynomial R))
    (fuel : ℕ := 2048)
    : Array (FMvPolynomial R)
```

**Optimizations implemented:**

- **Buchberger's first criterion**: if `lcm(in(f), in(g)) = in(f) + in(g)` (relatively
  prime leading monomials), skip this S-pair — guaranteed to reduce to 0.

**Future optimizations:**

- **Chain criterion (second criterion)**: if some `h ∈ G` has `in(h) | lcm(in(f),in(g))`
  and pairs `(f,h)` and `(g,h)` are already processed, skip `(f,g)`.
- **Interreduction**: reduce each basis element by the others to obtain a *reduced* Gröbner
  basis (the unique canonical form).

---

## Phase 5: Translation Layer

**New file:** `Fettuccine/Algorithm/Translate.lean`

Connects the algorithm layer to the existing formal layer for `n`-variable polynomials (`σ = Fin n`).

### Monomial translation

```lean
def FMonomial.toCMonomial (n : ℕ) (m : FMonomial) : CMonomial (Fin n) :=
  DFinsupp.equivFunOnFintype.symm (fun i => m.getD i.val 0)

def CMonomial.toFast (n : ℕ) (m : CMonomial (Fin n)) : FMonomial :=
  Array.ofFn (fun i : Fin n => m i)
```

Key lemmas needed:
- `toCMonomial_zero` : `zero n` maps to `0`
- `toCMonomial_add`  : translation respects addition
- `toCMonomial_degree` : translation preserves degree
- `toCMonomial_divides` : translation preserves divisibility
- Round-trip: `toFast (toCMonomial n m) = m` (for length-`n` arrays)

### Polynomial translation

```lean
def FMvPolynomial.toCMvPolynomial (n : ℕ) (f : FMvPolynomial R)
    : CMvPolynomial (Fin n) R :=
  f.foldl (fun acc (m, c) => acc + CMvPolynomial.ofMonomial (m.toCMonomial n) c) 0
```

Key lemmas:
- This is a ring homomorphism (preserves `+` and `*`).
- It maps a normalized `FMvPolynomial` injectively.

### Order compatibility

```lean
-- Fast lex corresponds to CMonomialOrder.lex
lemma lex_eq_lex (m₁ m₂ : FMonomial) (n : ℕ)
    (h₁ : m₁.size = n) (h₂ : m₂.size = n) :
    FMonomialOrder.lex m₁ m₂ = .lt ↔
    m₁.toCMonomial n ≺[CMonomialOrder.lex] m₂.toCMonomial n
```

Similarly for grlex and grevlex.

---

## Phase 6: Tactic Completion

**Updated:** `Fettuccine/Tactic.lean`

The tactic `groebnerBasis I ord` proceeds as follows:

1. Parse the goal — extract generators from `I = Ideal.span S`.
2. Translate generators to `FMvPolynomial`.
3. Run `buchberger` to obtain `G_fast`.
4. Translate `G_fast` back to `CMvPolynomial (Fin n) R` as `G_formal`.
5. Discharge `IsGroebnerBasis₁` using `native_decide` (works for concrete rings).
6. (Phase 7) Discharge `IsGroebnerBasis` via `buchberger.mpr`.

**Step 5** is the key: for concrete polynomial rings (specific `n`, field like `ℚ` or
`ZMod p`, explicit generators), `IsGroebnerBasis₁` is decidable given `DecidableEq` on
the coefficient field. `native_decide` discharges it in compiled code.

**Ideal membership certificate (condition 1 of `IsGroebnerBasis₁`):** each `g ∈ G_formal`
must be shown to lie in `I = Ideal.span {f₁,...,fₖ}`. Strategy: extend `buchberger`
to also output Bézout coefficients (a representation `g = Σᵢ pᵢ * fᵢ`), then prove
membership by `simp` using `Ideal.span` lemmas.

---

## Phase 7: Buchberger's Theorem (Mathematical)

**Modified:** `Fettuccine/Buchberger.lean`

This phase is **independent** of Phases 1–6 and can be developed in parallel.

Theorem to prove:
```lean
theorem buchberger (I : Ideal (CMvPolynomial σ R)) (G : List (CMvPolynomial σ R)) :
    IsGroebnerBasis ord I G ↔ IsGroebnerBasis₁ ord I G
```

### Direction `→` (easy)

- S-polynomials `S(f,g)` lie in `I` (since `f, g ∈ G ⊆ I`).
- By the Gröbner basis property, every element of `I` reduces to 0 mod `G`.
- Hence `S(f,g)` reduces to 0 mod `G`. ∎

### Direction `←` (hard)

Required chain of lemmas, in suggested development order:

**7.1. The S-polynomial leading-monomial lemma**

```lean
lemma sPolynomial_lt (f g : CMvPolynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0)
    (h : in[ord](f) = in[ord](g)) :
    in[ord](sPolynomial ord f g) ≺[ord] in[ord](f)  ∨  sPolynomial ord f g = 0
```

If `f` and `g` share the same leading monomial (after scaling), the S-polynomial has
strictly smaller leading monomial. This is the "cancellation" property that makes the
S-polynomial criterion work.

**7.2. Top combinations reduce to zero**

A *top combination* of `G` is a sum `Σ cᵢ * mᵢ * gᵢ` where all `cᵢ * mᵢ * in(gᵢ)` equal
the same monomial (i.e. the leading terms all cancel).

```lean
-- If all S-polynomials of G reduce to 0 mod G,
-- then every top combination of G also reduces to 0 mod G.
lemma topCombination_reducesToZero (G : List (CMvPolynomial σ R))
    (hS : ∀ f ∈ G, ∀ g ∈ G,
      (mvDivideₙ ord (sPolynomial ord f g) G ...).2 = 0)
    (f : CMvPolynomial σ R) (hf : IsTopCombination G f) :
    (mvDivideₙ ord f G ...).2 = 0
```

Proved by strong induction on the leading monomial of `f`, using 7.1 to reduce the leading
monomial at each step.

**7.3. Every element of `I` is a (generalized) top combination**

```lean
lemma idealMem_isTopCombination
    (G : List (CMvPolynomial σ R)) (f : CMvPolynomial σ R)
    (hf : f ∈ Ideal.span {g | g ∈ G}) :
    ∃ ... -- f can be expressed as a combination refining to a top combination
```

Any linear combination of elements of `G` can be re-expressed as a sum of top combinations
by grouping terms of the same leading monomial.

**7.4. Conclusion**

Combining 7.2 and 7.3: if all S-polynomials reduce to 0, then every element of `I` reduces
to 0 mod `G`, i.e. `in(I) ⊆ in(G)`. The reverse inclusion `in(G) ⊆ in(I)` is immediate
from `G ⊆ I`. This gives `in(I) = in(G)`, which is exactly `IsGroebnerBasis`. ∎

**Expected effort:** Phase 7 is the most mathematically intensive part. Steps 7.2 and 7.3
involve careful inductions that can become verbose in Lean. Estimate: 500–1000 lines.

---

## Suggested Implementation Order

| Priority | Phase | Effort | Unblocks |
|----------|-------|--------|----------|
| 1 | Phase 1: FMonomial/FMvPolynomial | Small | 2–6 | ✅ |
| 2 | Phase 2: Monomial Orders | Small | 3–4 | ✅ |
| 3 | Phase 3: Division | Medium | 4 | ✅ |
| 4 | Phase 4: Buchberger | Medium | 6 | ✅ |
| 5 | Phase 5: Translation Layer | Medium | 6 | |
| 6 | Phase 6: Updated Tactic | Medium | Working tactic | |
| 7 | Phase 7: Buchberger's Theorem | Large | Full `IsGroebnerBasis` | |

Phases 1–6 are essentially independent of Phase 7. After Phase 6 the tactic will work for
concrete goals (over `ℚ`, `ZMod p`, etc.) via `native_decide`. Phase 7 completes the
formal connection to the mathematical definition.

---

## Key Design Decisions

**D1: Variable representation.** `FMonomial = Array ℕ` is untyped. For the translation
in Phase 5, carry `n : ℕ` as an explicit parameter and add `m.size = n` hypotheses where
needed. (Alternative: `Vector ℕ n` — cleaner proofs but more verbose.)

**D2: Polynomial normalization.** Use unsorted arrays internally in the algorithm (simplest),
normalize before any leading-term access.

**D3: Reduced vs. non-reduced bases.** The basic algorithm produces a non-reduced Gröbner
basis. Add interreduction as an optional post-processing step after the basic version works.

---

## File Structure

```
Fettuccine/
  Algorithm/
    MvPolynomial.lean  -- FMonomial and FMvPolynomial: arithmetic, normalize ✅
    MonomialOrder.lean -- FMonomialOrder.{lex, grlex, grevlex}              ✅
    Divide.lean        -- FMvPolynomial.divide (fuel-bounded, no proof)     ✅
    Buchberger.lean    -- FMvPolynomial.{sPolynomial, buchberger}           ✅
    Translate.lean     -- toCMonomial, toCMvPolynomial, round-trip lemmas
```

Existing files (`CMvPolynomial.lean`, `CMonomialOrder.lean`, `Divide.lean`) are
**untouched** — the algorithm layer sits alongside them.
