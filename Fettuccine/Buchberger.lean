import Fettuccine.Algorithm.Buchberger
import Fettuccine.Groebner

/-!
# Buchberger's Algorithm

This file implements a safe interface for Buchberger's algorithm for computing Groebner bases of
ideals of `CMvPolynomial (Fin n) ℚ`, by evaluating and certifying a candidate basis computed by
using fast, vector-based types.
-/

variable {n : ℕ}

namespace FMonomial

/-- Convert a `FMonomial n` to a `CMonomial (Fin n)`. -/
def toCMonomial (m : FMonomial n) : CMonomial (Fin n) :=
  DFinsupp.equivFunOnFintype.symm fun i : Fin n => m.toArray.getD i.val 0

end FMonomial

namespace FMvPolynomial

/-- Convert a `FMvPolynomial n ℚ` to a `CMvPolynomial (Fin n)`. -/
def toCMvPolynomial (f : FMvPolynomial n ℚ) : CMvPolynomial (Fin n) ℚ :=
  f.map (fun (m, c) => CMvPolynomial.ofMonomial m.toCMonomial c) |>.sum

/-- Convert an array of fast polynomials to a list of `CMvPolynomial`s. -/
def toCMvPolynomialList (fs : Array (FMvPolynomial n ℚ)) : List (CMvPolynomial (Fin n) ℚ) :=
  fs.toList.map toCMvPolynomial

/-- Convert a two-dimensional array of fast polynomials to nested lists of `CMvPolynomial`s. -/
def toCMvPolynomialList₂ (fs : Array (Array (FMvPolynomial n ℚ))) :
    List (List (CMvPolynomial (Fin n) ℚ)) :=
  fs.toList.map toCMvPolynomialList

/-- Convert a three-dimensional array of fast polynomials to nested lists of `CMvPolynomial`s. -/
def toCMvPolynomialList₃ (fs : Array (Array (Array (FMvPolynomial n ℚ)))) :
    List (List (List (CMvPolynomial (Fin n) ℚ))) :=
  fs.toList.map toCMvPolynomialList₂

end FMvPolynomial

namespace CMonomial

/-- Convert a `CMonomial (Fin n)` to a `FMonomial n`. -/
def toFMonomial (m : CMonomial (Fin n)) : FMonomial n :=
  ⟨Array.ofFn fun i => m i, by simp⟩

end CMonomial

namespace CMvPolynomial

/-- Convert a `CMvPolynomial (Fin n) ℚ` to a `FMvPolynomial n ℚ`. -/
def toFMvPolynomial (f : CMvPolynomial (Fin n) ℚ) : FMvPolynomial n ℚ :=
  f.supportSorted CMonomialOrder.lex |>.toArray.map fun m =>
    (m.toFMonomial, f.coefficientOf m)

end CMvPolynomial

namespace Buchberger

/-- `f` is represented by the coefficient list `cs` as a linear combination of `gs`. -/
def IsLinearCombinationWith (f : CMvPolynomial (Fin n) ℚ) (gs cs : List (CMvPolynomial (Fin n) ℚ)) :
    Prop :=
  cs.length = gs.length ∧ f = Groebner.linearCombination gs cs

instance decidableIsLinearCombinationWith (f : CMvPolynomial (Fin n) ℚ)
    (gs cs : List (CMvPolynomial (Fin n) ℚ)) : Decidable (IsLinearCombinationWith f gs cs) := by
  unfold IsLinearCombinationWith
  infer_instance

/-- The raw witnesses transported back from the fast algorithm, awaiting verification by
    ``IsGroebnerBasisWith``. -/
structure Witness (n : ℕ) where
  bm : List (List (CMvPolynomial (Fin n) ℚ))
  sr : List (List (List (CMvPolynomial (Fin n) ℚ)))

/-- The C-level checked Buchberger certificate predicate. -/
def IsGroebnerBasisWith
    (tag : Type) [CMonomialOrder.CMonomialOrderTag tag (Fin n)]
    (I : List (CMvPolynomial (Fin n) ℚ)) -- the generators of the ideal
    (G : List (CMvPolynomial (Fin n) ℚ)) -- the candidate basis
    (witness : Witness n) : Prop :=
  witness.bm.length = G.length ∧
  (∀ i : Fin G.length,
    IsLinearCombinationWith (G.get i) I (witness.bm.getD i.val [])) ∧
  witness.sr.length = G.length ∧
  ∀ i : Fin G.length,
    let R := witness.sr.getD i.val []
    R.length = G.length ∧
      ∀ j : Fin G.length, i < j →
        Groebner.ReducesToZeroWith tag
          (CMvPolynomial.sPolynomial'
            (CMonomialOrder.CMonomialOrderTag.ord (tag := tag) (σ := Fin n))
            (G.get i) (G.get j))
          G (R.getD j.val [])

instance decidableIsGroebnerBasisWith
    (tag : Type) [CMonomialOrder.CMonomialOrderTag tag (Fin n)]
    (I : List (CMvPolynomial (Fin n) ℚ)) -- the generators of the ideal
    (G : List (CMvPolynomial (Fin n) ℚ)) -- the candidate basis
    (witness : Witness n) : Decidable (IsGroebnerBasisWith tag I G witness) := by
  unfold IsGroebnerBasisWith IsLinearCombinationWith
    Groebner.ReducesToZeroWith Groebner.linearCombination
  infer_instance

/-- Soundness: the previous predicate proves `IsGroebnerBasis`. -/
theorem isGroebnerBasisWith_sound
    {tag : Type} [CMonomialOrder.CMonomialOrderTag tag (Fin n)]
    {I : List (CMvPolynomial (Fin n) ℚ)} -- the generators of the ideal
    {G : List (CMvPolynomial (Fin n) ℚ)} -- the candidate basis
    {witness : Witness n}
    (h : IsGroebnerBasisWith tag I G witness) : Groebner.IsGroebnerBasis tag I G := by
  rcases h with ⟨_, h_mem, _, hS⟩
  constructor
  · intro i
    -- Since we've got an expression of each g ∈ G as a linear combination of the generators, this
    -- immediately implies that g ∈ ⟨I⟩.
    rcases h_mem i with ⟨_, heq⟩
    rw [heq]
    exact Groebner.linearCombination_mem_idealOf I (witness.bm.getD i.val [])
  · intro i j hij
    -- The quotients proving that S(gᵢ, gⱼ) reduces to zero are given by `sr[i][j]`, so we just have
    -- to pull that out...
    specialize hS i
    dsimp at hS
    rcases hS with ⟨_, hS⟩
    specialize hS j hij
    exact ⟨(witness.sr.getD i.val []).getD j.val [], hS⟩

/-- A Groebner basis of an ideal of a polynomial ring. -/
structure GroebnerBasis
    (tag : Type) [CMonomialOrder.CMonomialOrderTag tag (Fin n)]
    (I : List (CMvPolynomial (Fin n) ℚ)) where
  basis : List (CMvPolynomial (Fin n) ℚ)
  h : Groebner.IsGroebnerBasis tag I basis

/-- Compute a Groebner basis using `untrustedBuchberger`, and feed it through the verification
    procedure. -/
@[inline] def buchberger
    (tag : Type)
    -- Leverage the typeclass inference system to get the monomial order and the associated fast
    -- monomial order.
    [CMonomialOrder.CMonomialOrderTag tag (Fin n)]
    [CMonomialOrder.FMonomialOrderTag tag n]
    (I : List (CMvPolynomial (Fin n) ℚ))
    -- Again, this should be enough fuel, but it is configurable.
    (fuel : ℕ := 4096) : Option (GroebnerBasis tag I) :=
  let gb := FMvPolynomial.untrustedBuchberger
    (CMonomialOrder.FMonomialOrderTag.ord (tag := tag) (n := n))
    (I.toArray.map CMvPolynomial.toFMvPolynomial)
    fuel
  let basis := FMvPolynomial.toCMvPolynomialList gb.G
  let witness : Witness n :=
    { bm := FMvPolynomial.toCMvPolynomialList₂ gb.witness.bm
      sr := FMvPolynomial.toCMvPolynomialList₃ gb.witness.sr }
  if h : decide (IsGroebnerBasisWith tag I basis witness) = true then
    some {
      basis := basis
      h     := by
        have hs := isGroebnerBasisWith_sound (of_decide_eq_true h)
        simpa using hs
    }
  else
    none

end Buchberger
