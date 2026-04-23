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
def IsLinearCombinationWith
    (f : CMvPolynomial (Fin n) Rat)
    (gs cs : List (CMvPolynomial (Fin n) Rat)) : Prop :=
  cs.length = gs.length ∧ f = Groebner.linearCombination gs cs

instance decidableIsLinearCombinationWith
    (f : CMvPolynomial (Fin n) Rat)
    (gs cs : List (CMvPolynomial (Fin n) Rat)) :
    Decidable (IsLinearCombinationWith f gs cs) := by
  unfold IsLinearCombinationWith
  infer_instance

/-- Raw witnesses transported back from the fast algorithm. They are not trusted until checked by
`IsGroebnerBasisWith`. -/
structure Witness (n : ℕ) where
  bm : List (List (CMvPolynomial (Fin n) Rat))
  sr : List (List (List (CMvPolynomial (Fin n) Rat)))

/-- The C-level checked Buchberger certificate predicate. -/
def IsGroebnerBasisWith
    (tag : Type) [CMonomialOrder.CMonomialOrderTag tag (Fin n)]
    (gens basis : List (CMvPolynomial (Fin n) Rat)) (witness : Witness n) : Prop :=
  witness.bm.length = basis.length ∧
  (∀ i : Fin basis.length,
    IsLinearCombinationWith (basis.get i) gens (witness.bm.getD i.val [])) ∧
  witness.sr.length = basis.length ∧
  ∀ i : Fin basis.length,
    let row := witness.sr.getD i.val []
    row.length = basis.length ∧
    ∀ j : Fin basis.length, i < j →
      Groebner.ReducesToZeroWith tag
        (CMvPolynomial.sPolynomial'
          (CMonomialOrder.CMonomialOrderTag.ord (tag := tag) (σ := Fin n))
          (basis.get i) (basis.get j))
        basis (row.getD j.val [])

instance decidableIsGroebnerBasisWith
    (tag : Type) [CMonomialOrder.CMonomialOrderTag tag (Fin n)]
    (gens basis : List (CMvPolynomial (Fin n) Rat)) (witness : Witness n) :
    Decidable (IsGroebnerBasisWith tag gens basis witness) := by
  unfold IsGroebnerBasisWith IsLinearCombinationWith
    Groebner.ReducesToZeroWith Groebner.linearCombination
  infer_instance

theorem isGroebnerBasisWith_sound
    {tag : Type} [CMonomialOrder.CMonomialOrderTag tag (Fin n)]
    {gens basis : List (CMvPolynomial (Fin n) Rat)} {witness : Witness n}
    (h : IsGroebnerBasisWith tag gens basis witness) :
    Groebner.IsGroebnerBasis tag gens basis := by
  rcases h with ⟨_hbm, hmem, _hsr, hspolys⟩
  constructor
  · intro i
    rcases hmem i with ⟨_, heq⟩
    rw [heq]
    exact Groebner.linearCombination_mem_idealOf gens (witness.bm.getD i.val [])
  · intro i j hij
    specialize hspolys i
    dsimp at hspolys
    rcases hspolys with ⟨hrow, hspolys⟩
    specialize hspolys j hij
    exact ⟨(witness.sr.getD i.val []).getD j.val [], hspolys⟩

/-- A checked Groebner basis in the `CMvPolynomial` layer. -/
structure GroebnerBasis
    (I : List (CMvPolynomial (Fin n) Rat))
    (tag : Type) [CMonomialOrder.CMonomialOrderTag tag (Fin n)] where
  basis : List (CMvPolynomial (Fin n) Rat)
  h : Groebner.IsGroebnerBasis tag I basis

/-- Compute and check a Groebner basis using the monomial order selected by `tag`.

The fast algorithm is fuel-bounded and untrusted, so this returns `none` if the transported witness
does not pass the `CMvPolynomial` checker. -/
@[inline] def buchberger
    (tag : Type)
    [CMonomialOrder.CMonomialOrderTag tag (Fin n)]
    [CMonomialOrder.FMonomialOrderTag tag n]
    (I : List (CMvPolynomial (Fin n) Rat)) (fuel : ℕ := 4096) :
    Option (GroebnerBasis I tag) :=
  let gensF := I.toArray.map CMvPolynomial.toFMvPolynomial
  let gbF := FMvPolynomial.untrustedBuchberger'
    (CMonomialOrder.FMonomialOrderTag.ord (tag := tag) (n := n)) gensF fuel
  let basis := FMvPolynomial.toCMvPolynomialList gbF.G
  let witness : Witness n :=
    { bm := FMvPolynomial.toCMvPolynomialList₂ gbF.witness.i
      sr := FMvPolynomial.toCMvPolynomialList₃ gbF.witness.j }
  if h : decide (IsGroebnerBasisWith tag I basis witness) = true then
    some
      { basis := basis
        h := by
          have hs := isGroebnerBasisWith_sound (of_decide_eq_true h)
          simpa using hs }
  else
    none

end Buchberger
