import Fettuccine.CMonomialOrder
import Fettuccine.CMvPolynomial

/-!
# Multivariate Polynomial Division

This file defines the division algorithm for `CMvPolynomial σ R` with respect to a monomial order.
-/

namespace CMonomial

variable {σ : Type*} [DecidableEq σ]

-- Predicate for monomial divisibility: `m₁` divides `m₂`.
def divides? (m₁ m₂ : CMonomial σ) : Prop :=
  ∀ i ∈ m₁.support, m₁ i ≤ m₂ i

instance (m₁ m₂ : CMonomial σ) : Decidable (divides? m₁ m₂) := by
  classical
  refine decidable_of_iff (∀ i : {i // i ∈ m₁.support}, m₁ i ≤ m₂ i) ?_
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h i
    exact h i i.property

/-- Divide monomials when possible, returning the quotient. -/
def divide (m₁ m₂ : CMonomial σ) : Option (CMonomial σ) :=
  if _ : divides? m₂ m₁ then
    some (m₁ - m₂)
  else
    none

lemma divides?_iff (m₁ m₂ : CMonomial σ) : divides? m₁ m₂ ↔ ∀ i, m₁ i ≤ m₂ i := by
  constructor
  · intro h i
    by_cases hi : i ∈ m₁.support
    · exact h i hi
    · have hzero : m₁ i = 0 := by
        simpa using (DFinsupp.notMem_support_iff).mp hi
      simp [hzero]
  · intro h i hi
    exact h i

lemma divides?_lcm_left (m₁ m₂ : CMonomial σ) : divides? m₁ (lcm m₁ m₂) := by
  intro i hi
  simp [lcm, DFinsupp.zipWith_apply]

lemma divides?_lcm_right (m₁ m₂ : CMonomial σ) : divides? m₂ (lcm m₁ m₂) := by
  intro i hi
  simp [lcm, DFinsupp.zipWith_apply]

lemma divide_eq_some_of_divides? {m₁ m₂ : CMonomial σ} (h : divides? m₂ m₁) :
    m₁.divide m₂ = some (m₁ - m₂) := by
  simp [divide, h]

end CMonomial
