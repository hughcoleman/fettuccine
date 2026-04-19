import Fettuccine.Algorithm.Buchberger
import Mathlib.Algebra.Field.Rat

/-!
# Certification for Computable Gröbner Bases

This file defines proof-bearing certificates for the array-backed polynomial implementation.
The fast Buchberger implementation is used only to generate witnesses; certificates are accepted
only after finite checks have been converted into proof fields.
-/

namespace FMvPolynomial

variable {n : ℕ}

-- `decide` needs a constructive `Decidable (∀ i : Fin n, p i)`.
instance decidableForallFin {m : Nat} {p : Fin m → Prop} [DecidablePred p] :
    Decidable (∀ i, p i) :=
  Nat.decidableForallFin (P := p)

/-- A finite linear combination of array-backed polynomials. -/
def linearCombination (ord : FMonomial n → FMonomial n → Ordering)
    (terms : Array (FMvPolynomial n Rat))
    (coefficients : Fin terms.size → FMvPolynomial n Rat) :
    FMvPolynomial n Rat :=
  Id.run do
    let mut acc : FMvPolynomial n Rat := #[]
    for h : i in [:terms.size] do
      acc := add ord acc (mul ord (coefficients ⟨i, h.upper⟩) terms[i])
    return acc

/-- Equality after normalization. -/
def equalNormalized (ord : FMonomial n → FMonomial n → Ordering)
    (f g : FMvPolynomial n Rat) : Prop :=
  normalize ord f = normalize ord g

instance decidableEqualNormalized (ord : FMonomial n → FMonomial n → Ordering)
    (f g : FMvPolynomial n Rat) : Decidable (equalNormalized ord f g) := by
  unfold equalNormalized
  infer_instance

/-- Boolean test for normalized equality. -/
def equalNormalized? (ord : FMonomial n → FMonomial n → Ordering)
    (f g : FMvPolynomial n Rat) : Bool :=
  decide (equalNormalized ord f g)

/-- A polynomial coefficient vector indexed by the original generators. -/
abbrev MembershipVector (n : ℕ) := Array (FMvPolynomial n Rat)

private def zeroMembershipVector (k : Nat) : MembershipVector n :=
  Array.replicate k #[]

private def unitMembershipVector (k i : Nat) : MembershipVector n :=
  (zeroMembershipVector (n := n) k).set! i #[(FMonomial.zero n, 1)]

private def membershipVectorAdd (ord : FMonomial n → FMonomial n → Ordering)
    (a b : MembershipVector n) : MembershipVector n :=
  Id.run do
    let size := max a.size b.size
    let mut out : MembershipVector n := #[]
    for i in [:size] do
      out := out.push (add ord (a.getD i #[]) (b.getD i #[]))
    return out

private def membershipVectorSub (ord : FMonomial n → FMonomial n → Ordering)
    (a b : MembershipVector n) : MembershipVector n :=
  Id.run do
    let size := max a.size b.size
    let mut out : MembershipVector n := #[]
    for i in [:size] do
      out := out.push (sub ord (a.getD i #[]) (b.getD i #[]))
    return out

private def membershipVectorMulMonomial (ord : FMonomial n → FMonomial n → Ordering)
    (m : FMonomial n) (c : Rat) (a : MembershipVector n) : MembershipVector n :=
  a.map fun p => mulMonomial ord m c p

private def membershipVectorMulPolynomial (ord : FMonomial n → FMonomial n → Ordering)
    (q : FMvPolynomial n Rat) (a : MembershipVector n) : MembershipVector n :=
  a.map fun p => mul ord q p

private def membershipVectorLinearCombination (ord : FMonomial n → FMonomial n → Ordering)
    (qs : Array (FMvPolynomial n Rat)) (vectors : Array (MembershipVector n))
    (size : Nat) : MembershipVector n :=
  Id.run do
    let mut acc := zeroMembershipVector (n := n) size
    for i in [:vectors.size] do
      let scaled := membershipVectorMulPolynomial ord (qs.getD i #[]) (vectors.getD i #[])
      acc := membershipVectorAdd ord acc scaled
    return acc

private def sPolynomialMembershipVector (ord : FMonomial n → FMonomial n → Ordering)
    (f g : FMvPolynomial n Rat) (vf vg : MembershipVector n) : MembershipVector n :=
  match f[0]?, g[0]? with
  | some (lm_f, lc_f), some (lm_g, lc_g) =>
    let lcm := FMonomial.lcm lm_f lm_g
    let mf := (lcm.divide lm_f).getD (FMonomial.zero n)
    let mg := (lcm.divide lm_g).getD (FMonomial.zero n)
    membershipVectorSub ord
      (membershipVectorMulMonomial ord mf lc_g vf)
      (membershipVectorMulMonomial ord mg lc_f vg)
  | _, _ =>
    zeroMembershipVector (n := n) vf.size

private def remainderMembershipVector (ord : FMonomial n → FMonomial n → Ordering)
    (f g : FMvPolynomial n Rat) (vf vg : MembershipVector n)
    (basisVectors : Array (MembershipVector n)) (qs : Array (FMvPolynomial n Rat))
    (gensSize : Nat) : MembershipVector n :=
  membershipVectorSub ord
    (sPolynomialMembershipVector ord f g vf vg)
    (membershipVectorLinearCombination ord qs basisVectors gensSize)

private def initialBasisWithMembership (ord : FMonomial n → FMonomial n → Ordering)
    (gens : Array (FMvPolynomial n Rat)) :
    Array (FMvPolynomial n Rat × MembershipVector n) :=
  Id.run do
    let mut out : Array (FMvPolynomial n Rat × MembershipVector n) := #[]
    for h : i in [:gens.size] do
      let g := normalize ord gens[i]
      if g.size > 0 then
        out := out.push (g, unitMembershipVector (n := n) gens.size i)
    return out

private def basisOfTracked
    (tracked : Array (FMvPolynomial n Rat × MembershipVector n)) :
    Array (FMvPolynomial n Rat) :=
  tracked.map Prod.fst

private def vectorsOfTracked
    (tracked : Array (FMvPolynomial n Rat × MembershipVector n)) :
    Array (MembershipVector n) :=
  tracked.map Prod.snd

/-- Witness data for ideal membership of the computed basis. -/
structure IdealMembershipCertificateWitnesses (n : ℕ) where
  coefficients : Array (Array (FMvPolynomial n Rat))

/-- Witness data for reduction of all final S-polynomials. -/
structure SPolynomialsReduceCertificateWitnesses (n : ℕ) where
  quotients : Array (Array (Array (FMvPolynomial n Rat)))

/-- Witness data emitted by the computable Buchberger wrapper. -/
structure GroebnerBasisCertificateWitnesses (n : ℕ) where
  basis : Array (FMvPolynomial n Rat)
  h_mem : IdealMembershipCertificateWitnesses n
  h_sPolynomials : SPolynomialsReduceCertificateWitnesses n

private def pairQuotients (ord : FMonomial n → FMonomial n → Ordering)
    (basis : Array (FMvPolynomial n Rat)) (i j : Nat) : Array (FMvPolynomial n Rat) :=
  let f := basis.getD i #[]
  let g := basis.getD j #[]
  (mvDivide ord (sPolynomial ord f g) basis).1

private def allSPolynomialWitnesses (ord : FMonomial n → FMonomial n → Ordering)
    (basis : Array (FMvPolynomial n Rat)) : SPolynomialsReduceCertificateWitnesses n :=
  { quotients :=
      Id.run do
        let mut out : Array (Array (Array (FMvPolynomial n Rat))) := #[]
        for i in [:basis.size] do
          let mut row : Array (Array (FMvPolynomial n Rat)) := #[]
          for j in [:basis.size] do
            row := row.push (pairQuotients ord basis i j)
          out := out.push row
        return out }

/-- Buchberger with separately checkable certificate witnesses. -/
def buchbergerWithCertificateWitnesses
    (ord : FMonomial n → FMonomial n → Ordering)
    (gens : Array (FMvPolynomial n Rat)) (fuel : Nat := 2048) :
    GroebnerBasisCertificateWitnesses n :=
  let tracked₀ := initialBasisWithMembership ord gens
  let pairs₀ : Array (Nat × Nat) :=
    Id.run do
      let mut pairs : Array (Nat × Nat) := #[]
      for j in [:tracked₀.size] do
        for i in [:j] do
          pairs := pairs.push (i, j)
      return pairs
  let extPairs (pairs : Array (Nat × Nat)) (i' : Nat) : Array (Nat × Nat) :=
    Id.run do
      let mut pairs' := pairs
      for k in [:i'] do
        pairs' := pairs'.push (k, i')
      return pairs'
  let rec loop (fuel : Nat) (tracked : Array (FMvPolynomial n Rat × MembershipVector n))
      (pairs : Array (Nat × Nat)) (ptr : Nat) :
      Array (FMvPolynomial n Rat × MembershipVector n) :=
    match fuel with
    | 0 => tracked
    | fuel + 1 =>
      match pairs[ptr]? with
      | none => tracked
      | some (i, j) =>
        match tracked[i]?, tracked[j]? with
        | some (f, vf), some (g, vg) =>
          match f[0]?, g[0]? with
          | some (lmf, _), some (lmg, _) =>
            if lmf.relativelyPrime? lmg then
              loop fuel tracked pairs (ptr + 1)
            else
              let basis := basisOfTracked tracked
              let vectors := vectorsOfTracked tracked
              let (qs, r) := mvDivide ord (sPolynomial ord f g) basis
              if r.size == 0 then
                loop fuel tracked pairs (ptr + 1)
              else
                let vr := remainderMembershipVector ord f g vf vg vectors qs gens.size
                let tracked' := tracked.push (r, vr)
                let pairs' := extPairs pairs tracked.size
                loop fuel tracked' pairs' (ptr + 1)
          | _, _ => loop fuel tracked pairs (ptr + 1)
        | _, _ => loop fuel tracked pairs (ptr + 1)
  let tracked := loop fuel tracked₀ pairs₀ 0
  let basis := basisOfTracked tracked
  { basis := basis
    h_mem := { coefficients := vectorsOfTracked tracked }
    h_sPolynomials := allSPolynomialWitnesses ord basis }

end FMvPolynomial

open FMvPolynomial

variable {n : ℕ}

/-- Proof-bearing ideal membership certificate for each basis element. -/
structure IdealMembershipCertificate
    (ord : FMonomial n → FMonomial n → Ordering)
    (gens basis : Array (FMvPolynomial n Rat)) where
  coefficients :
    Fin basis.size → Fin gens.size → FMvPolynomial n Rat
  h_mem :
    ∀ i : Fin basis.size,
      FMvPolynomial.equalNormalized ord
        basis[i]
        (FMvPolynomial.linearCombination ord gens (coefficients i))

/-- Proof-bearing certificate that all S-polynomials reduce to zero. -/
structure SPolynomialsReduceCertificate
    (ord : FMonomial n → FMonomial n → Ordering)
    (basis : Array (FMvPolynomial n Rat)) where
  quotients :
    Fin basis.size → Fin basis.size → Fin basis.size → FMvPolynomial n Rat
  h_sPolynomials :
    ∀ i j : Fin basis.size, i ≠ j →
      FMvPolynomial.equalNormalized ord
        (FMvPolynomial.sPolynomial ord basis[i] basis[j])
        (FMvPolynomial.linearCombination ord basis (quotients i j))

/-- Proof-bearing certificate for the computable Buchberger criterion. -/
structure GroebnerBasisCertificate
    (ord : FMonomial n → FMonomial n → Ordering) where
  gens : Array (FMvPolynomial n Rat)
  basis : Array (FMvPolynomial n Rat)
  h_mem : IdealMembershipCertificate ord gens basis
  h_sPolynomials : SPolynomialsReduceCertificate ord basis

/-- Project-level certificate predicate: ideal membership plus Buchberger S-polynomial checks. -/
def IsGroebnerBasis'
    (ord : FMonomial n → FMonomial n → Ordering)
    (gens basis : Array (FMvPolynomial n Rat)) : Prop :=
  (∃ _c : IdealMembershipCertificate ord gens basis, True) ∧
  (∃ _c : SPolynomialsReduceCertificate ord basis, True)

namespace GroebnerBasisCertificate

theorem isGroebnerBasis'
    {ord : FMonomial n → FMonomial n → Ordering}
    (cert : GroebnerBasisCertificate ord) :
    IsGroebnerBasis' ord cert.gens cert.basis :=
  ⟨⟨cert.h_mem, trivial⟩, ⟨cert.h_sPolynomials, trivial⟩⟩

end GroebnerBasisCertificate

namespace IdealMembershipCertificate

private def coefficientsOfWitnesses
    {gens basis : Array (FMvPolynomial n Rat)}
    (w : FMvPolynomial.IdealMembershipCertificateWitnesses n)
    (i : Fin basis.size) (j : Fin gens.size) : FMvPolynomial n Rat :=
  (w.coefficients.getD i.val #[]).getD j.val #[]

def WitnessesValid
    (ord : FMonomial n → FMonomial n → Ordering)
    (gens basis : Array (FMvPolynomial n Rat))
    (w : FMvPolynomial.IdealMembershipCertificateWitnesses n) : Prop :=
  w.coefficients.size = basis.size ∧
    (∀ i : Fin basis.size, (w.coefficients.getD i.val #[]).size = gens.size) ∧
    ∀ i : Fin basis.size,
      FMvPolynomial.equalNormalized ord
        basis[i]
        (FMvPolynomial.linearCombination ord gens (coefficientsOfWitnesses w i))

instance decidableWitnessesValid
    (ord : FMonomial n → FMonomial n → Ordering)
    (gens basis : Array (FMvPolynomial n Rat))
    (w : FMvPolynomial.IdealMembershipCertificateWitnesses n) :
    Decidable (WitnessesValid ord gens basis w) := by
  unfold WitnessesValid
  infer_instance

def checkIdealMembershipCertificateWitnesses
    (ord : FMonomial n → FMonomial n → Ordering)
    (gens basis : Array (FMvPolynomial n Rat))
    (w : FMvPolynomial.IdealMembershipCertificateWitnesses n) : Bool :=
  decide (WitnessesValid ord gens basis w)

def ofWitnesses
    (ord : FMonomial n → FMonomial n → Ordering)
    (gens basis : Array (FMvPolynomial n Rat))
    (w : FMvPolynomial.IdealMembershipCertificateWitnesses n)
    (h : checkIdealMembershipCertificateWitnesses ord gens basis w = true) :
    IdealMembershipCertificate ord gens basis :=
  { coefficients := coefficientsOfWitnesses w
    h_mem := by
      have hv : WitnessesValid ord gens basis w := of_decide_eq_true (p :=
        WitnessesValid ord gens basis w) (by
          simpa [checkIdealMembershipCertificateWitnesses] using h)
      exact hv.2.2 }

end IdealMembershipCertificate

namespace SPolynomialsReduceCertificate

private def quotientsOfWitnesses
    {basis : Array (FMvPolynomial n Rat)}
    (w : FMvPolynomial.SPolynomialsReduceCertificateWitnesses n)
    (i j k : Fin basis.size) : FMvPolynomial n Rat :=
  ((w.quotients.getD i.val #[]).getD j.val #[]).getD k.val #[]

def WitnessesValid
    (ord : FMonomial n → FMonomial n → Ordering)
    (basis : Array (FMvPolynomial n Rat))
    (w : FMvPolynomial.SPolynomialsReduceCertificateWitnesses n) : Prop :=
  w.quotients.size = basis.size ∧
    (∀ i : Fin basis.size, (w.quotients.getD i.val #[]).size = basis.size) ∧
    (∀ i j : Fin basis.size,
      ((w.quotients.getD i.val #[]).getD j.val #[]).size = basis.size) ∧
    ∀ i j : Fin basis.size, i ≠ j →
      FMvPolynomial.equalNormalized ord
        (FMvPolynomial.sPolynomial ord basis[i] basis[j])
        (FMvPolynomial.linearCombination ord basis (quotientsOfWitnesses w i j))

instance decidableWitnessesValid
    (ord : FMonomial n → FMonomial n → Ordering)
    (basis : Array (FMvPolynomial n Rat))
    (w : FMvPolynomial.SPolynomialsReduceCertificateWitnesses n) :
    Decidable (WitnessesValid ord basis w) := by
  unfold WitnessesValid
  infer_instance

def checkSPolynomialsReduceCertificateWitnesses
    (ord : FMonomial n → FMonomial n → Ordering)
    (basis : Array (FMvPolynomial n Rat))
    (w : FMvPolynomial.SPolynomialsReduceCertificateWitnesses n) : Bool :=
  decide (WitnessesValid ord basis w)

def ofWitnesses
    (ord : FMonomial n → FMonomial n → Ordering)
    (basis : Array (FMvPolynomial n Rat))
    (w : FMvPolynomial.SPolynomialsReduceCertificateWitnesses n)
    (h : checkSPolynomialsReduceCertificateWitnesses ord basis w = true) :
    SPolynomialsReduceCertificate ord basis :=
  { quotients := quotientsOfWitnesses w
    h_sPolynomials := by
      have hv : WitnessesValid ord basis w := of_decide_eq_true (p :=
        WitnessesValid ord basis w) (by
          simpa [checkSPolynomialsReduceCertificateWitnesses] using h)
      exact hv.2.2.2 }

end SPolynomialsReduceCertificate

export IdealMembershipCertificate (checkIdealMembershipCertificateWitnesses)
export SPolynomialsReduceCertificate (checkSPolynomialsReduceCertificateWitnesses)
