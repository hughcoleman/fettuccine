import Aesop
import Mathlib.Data.Finsupp.Basic
import Mathlib.Order.Basic

/-!
# Multivariate polynomials

This file defines computable types for operating on multivariate polynomials
over commutative rings.

## Definitions

- `MvPolynomial σ R`: the type of polynomials with variables of type `σ` and
  variables in a commutative semiring `R`.
-/

/-- A monomial with variables `σ`. -/
private structure CMonomial (σ : Type*) [LinearOrder σ] where
  /-- The underlying list of variable-exponent pairs. -/
  lst : List (σ × ℕ)
  /-- The statement that this representation is sorted, meaning that the terms
  are arranged in **decreasing** order. -/
  is_sorted : lst.Pairwise (·.1 > ·.1)
  /-- The statement that the representation is reduced, meaning that there are
  no trivial terms. -/
  is_reduced : ∀ xn ∈ lst, xn.2 ≠ 0

namespace CMonomial

variable {σ : Type*} [LinearOrder σ]

/-- The unit monomial. -/
def one : CMonomial σ := ⟨[], by simp, by simp⟩

/-- Create a monomial from a variable and an exponent. -/
def ofVarExp (x : σ) (n : ℕ) (hn : n ≠ 0) : CMonomial σ := ⟨[(x, n)], by simp, by aesop⟩

/-- Create a linear monomial from a variable. -/
def ofVar (x : σ) : CMonomial σ := ofVarExp x 1 (by simp)

/-- We can prepend a variable to a monomial, so long as it is greater than all
existing variables. -/
def cons_gt (x : σ) (n : ℕ) (m : CMonomial σ) (hx : ∀ p ∈ m.lst, x > p.1) (hn : n ≠ 0) :
    CMonomial σ where
  lst         := (x, n) :: m.lst
  is_sorted   := List.pairwise_cons.mpr ⟨hx, m.is_sorted⟩
  is_reduced  := List.forall_mem_cons.mpr ⟨hn, m.is_reduced⟩

/-- The tail of a monomial is a monomial. -/
def tail (m : CMonomial σ) : CMonomial σ where
  lst         := m.lst.tail
  is_sorted   := m.is_sorted.tail
  is_reduced  := by
    intro xn h
    exact m.is_reduced xn (List.mem_of_mem_tail h)

-- Computation of the product of monomials.
section Mul

private structure CMonomialMul (a b : CMonomial σ) where
  /-- The product monomial. -/
  ab : CMonomial σ
  /-- A proof of an invariant property of multiplication, needed in the proof
  that `ab` is a monomial. -/
  is_mul (x : σ) (ha : ∀ p ∈ a.lst, x > p.1) (hb : ∀ p ∈ b.lst, x > p.1) :
    ∀ p ∈ ab.lst, x > p.1

def mul' (a b : CMonomial σ) : CMonomialMul a b := by
  match ha : a.lst, hb : b.lst with
  | _, [] => exact ⟨a, fun _ h _ => ha ▸ h⟩
  | [], _ => exact ⟨b, fun _ _ h => hb ▸ h⟩
  | (x, nx) :: as, (y, ny) :: bs =>
    sorry

/-- Compute the product of two monomials. -/
def mul (a b : CMonomial σ) : CMonomial σ :=
  (mul' a b).ab

-- def mx1 : CMonomial (Fin 2) := ofVar 0
-- def mx2 : CMonomial (Fin 2) := ofVarExp 0 2 (by simp)
-- def my1 : CMonomial (Fin 2) := ofVar 1
-- def mx3y1 : CMonomial (Fin 2) := mul (mul mx1 my1) mx2

end Mul

-- Computation of the lowest common multiple of monomials.
section LCM

end LCM

-- Computation of the quotient of monomials.
section Div

end Div

-- The equivalence of `CMonomial σ` and `σ →₀ ℕ`.
section Equiv

/-- Lift a `CMonomial σ` to a `σ →₀ ℕ` -/
noncomputable def toFinsupp (m : CMonomial σ) : σ →₀ ℕ :=
  m.lst.toFinset.sum (fun (x, n) => Finsupp.single x n)

/-- Reduce a `σ →₀ ℕ` to a `CMonomial σ`. -/
noncomputable def ofFinsupp (m : σ →₀ ℕ) : CMonomial σ where
  lst         := m.support.val.toList.map (fun x => (x, m x))
  is_sorted   := by
    sorry
  is_reduced  := by aesop

/-- A monomial function can be recovered from its finite support. -/
lemma ofFinsupp_toFinsupp (m : σ →₀ ℕ) : (ofFinsupp m).toFinsupp = m := by
  sorry

/-- A monomial can be recovered from its monomial function. -/
lemma toFinsupp_ofFinsupp (m : CMonomial σ) : ofFinsupp (toFinsupp m) = m := by
  sorry

/-- The equivalence between monomials and finitely-supported monomial functions. -/
noncomputable def equivFinsupp : CMonomial σ ≃ (σ →₀ ℕ) where
  toFun     := toFinsupp
  invFun    := ofFinsupp
  left_inv  := toFinsupp_ofFinsupp
  right_inv := ofFinsupp_toFinsupp

end Equiv

end CMonomial
