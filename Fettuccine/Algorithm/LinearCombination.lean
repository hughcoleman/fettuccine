import Fettuccine.Algorithm.FMonomialOrder

/-!
# Linear Combinations and Reduction

This file defines the notion of linear combinations and provides witness-checked certification
procedures.
-/

namespace FMvPolynomial

variable {n : ℕ}
variable {R : Type*} [DecidableEq R] [Zero R] [AddMonoid R]

namespace LinearCombination

/-- `f` is a linear combination of `gs`, with coefficients `cs`. -/
def IsLinearCombinationWith [Mul R] (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R))
  (cs : Array (FMvPolynomial n R)) : Prop := cs.size = gs.size ∧ equal? f S
where
  S := (Array.zipWith (fun g c => mul c g) gs cs) |> Array.foldl add #[]

instance decidableIsLinearCombinationWith [Mul R]
    (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R)) (cs : Array (FMvPolynomial n R)) :
    Decidable (IsLinearCombinationWith f gs cs) := by
  unfold IsLinearCombinationWith
  infer_instance

/-- `f` is a linear combination of `gs` when there exists a suitable witness. -/
def IsLinearCombination [Mul R] (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R)) : Prop :=
  ∃ cs : Array (FMvPolynomial n R), IsLinearCombinationWith f gs cs

namespace IsLinearCombination

structure Certificate [Mul R] (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R)) where
  cs : Array (FMvPolynomial n R)
  h  : IsLinearCombinationWith f gs cs

theorem sound [Mul R] {f : FMvPolynomial n R} {gs : Array (FMvPolynomial n R)}
    (cert : Certificate f gs) : IsLinearCombination f gs :=
  ⟨cert.cs, cert.h⟩

/-- Construct a certificate from a witness. -/
def ofWitness [Mul R] (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R))
    (cs : Array (FMvPolynomial n R)) (h : IsLinearCombinationWith f gs cs) : Certificate f gs :=
  { cs := cs
    h  := h }

end IsLinearCombination

end LinearCombination

namespace Division

open LinearCombination

/-- The leading monomial of `f` is not greater than that of `g`. -/
def LeadingMonomialNotGreater (ord : FMonomialOrder n) (f g : FMvPolynomial n R) : Prop :=
  match f.leadingMonomial ord, g.leadingMonomial ord with
  | none, _           => True
  | some _, none      => False
  | some mf, some mg  => ord mf mg ≠ .gt

instance decidableLeadingMonomialNotGreater (ord : FMonomialOrder n)
    (f g : FMvPolynomial n R) : Decidable (LeadingMonomialNotGreater ord f g) := by
  unfold LeadingMonomialNotGreater
  cases hf : f.leadingMonomial ord <;> cases hg : g.leadingMonomial ord
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse (by intro h; cases h)
  · infer_instance

/-- `f` reduces to zero modulo `gs` with respect to the monomial order `ord` if `f` is a linear
    combination of `gs`, and, the leading monomials satisfy certain conditions. -/
def ReducesToZeroWith [Mul R] (ord : FMonomialOrder n)
    (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R))
    (qs : Array (FMvPolynomial n R)) : Prop :=
  IsLinearCombinationWith f gs qs ∧
    ∀ p ∈ (Array.zipWith (fun g q => mul q g) gs qs),
      p.size = 0 ∨ LeadingMonomialNotGreater ord p f

instance decidableReducesToZeroWith [Mul R] (ord : FMonomialOrder n)
    (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R)) (qs : Array (FMvPolynomial n R)) :
    Decidable (ReducesToZeroWith ord f gs qs) := by
  unfold ReducesToZeroWith
  infer_instance

def ReducesToZero [Mul R] (ord : FMonomialOrder n)
    (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R)) : Prop :=
  ∃ qs : Array (FMvPolynomial n R), ReducesToZeroWith ord f gs qs

namespace ReducesToZero

structure Certificate [Mul R] (ord : FMonomialOrder n)
    (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R)) where
  qs : Array (FMvPolynomial n R)
  h  : ReducesToZeroWith ord f gs qs

theorem sound [Mul R] {ord : FMonomialOrder n} {f : FMvPolynomial n R}
    {gs : Array (FMvPolynomial n R)} (cert : Certificate ord f gs) : ReducesToZero ord f gs :=
  ⟨cert.qs, cert.h⟩

/-- Construct a certificate from a witness. -/
def ofWitness [Mul R] (ord : FMonomialOrder n)
    (f : FMvPolynomial n R) (gs : Array (FMvPolynomial n R))
    (qs : Array (FMvPolynomial n R)) (h : ReducesToZeroWith ord f gs qs) : Certificate ord f gs :=
  { qs := qs
    h  := h }

end ReducesToZero

end Division

end FMvPolynomial
