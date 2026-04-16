import Fettuccine.CMonomialOrder.Grlex

/-!
# The Graded Reverse Lexicographic Order on Monomials

This file provides an implementation of the graded reverse lexicographic order on monomials.

## Definitions

* `Grevlex ι` : a type synonym used to equip a type with the graded reverse lexicographic order.
* `toGrevlex` : additive equivalence from monomials to the `Grevlex` synonym.
* `CMonomialOrder.grevlex` : the graded reverse lexicographic monomial order on `CMonomial σ`.

## Theorems

This file currently focuses on constructing the order itself.
-/

/-- A type synonym to equip monomials with graded reverse lexicographic order. -/
abbrev Grevlex (ι : Type*) := Grlex (Π₀ _ : ιᵒᵈ, ℕ)

variable {σ : Type*} [DecidableEq σ]

/-- Reindex a monomial from `σ` to `σᵒᵈ` by `OrderDual.ofDual`. -/
def toDualMonomial : CMonomial σ → CMonomial σᵒᵈ :=
  DFinsupp.comapDomain' OrderDual.ofDual OrderDual.toDual_ofDual

/-- Reindex a monomial from `σᵒᵈ` back to `σ` by `OrderDual.toDual`. -/
def ofDualMonomial : CMonomial σᵒᵈ → CMonomial σ :=
  DFinsupp.comapDomain' OrderDual.toDual OrderDual.ofDual_toDual

@[simp] theorem toDualMonomial_apply (m : CMonomial σ) (i : σᵒᵈ) :
    toDualMonomial m i = m (OrderDual.ofDual i) :=
  by
    simpa [toDualMonomial] using
      (DFinsupp.comapDomain'_apply
        (β := fun _ : σ => ℕ)
        OrderDual.ofDual
        (hh' := OrderDual.toDual_ofDual)
        m i)

@[simp] theorem ofDualMonomial_apply (m : CMonomial σᵒᵈ) (i : σ) :
    ofDualMonomial m i = m (OrderDual.toDual i) :=
  by
    simpa [ofDualMonomial] using
      (DFinsupp.comapDomain'_apply
        (β := fun _ : σᵒᵈ => ℕ)
        OrderDual.toDual
        (hh' := OrderDual.ofDual_toDual)
        m i)

@[simp] theorem toDualMonomial_zero : toDualMonomial (0 : CMonomial σ) = 0 := by
  ext i
  simp [toDualMonomial]

@[simp] theorem ofDualMonomial_zero : ofDualMonomial (0 : CMonomial σᵒᵈ) = 0 := by
  ext i
  simp [ofDualMonomial]

@[simp] theorem toDualMonomial_add (a b : CMonomial σ) :
    toDualMonomial (a + b) = toDualMonomial a + toDualMonomial b := by
  ext i
  simp [toDualMonomial]

@[simp] theorem ofDualMonomial_add (a b : CMonomial σᵒᵈ) :
    ofDualMonomial (a + b) = ofDualMonomial a + ofDualMonomial b := by
  ext i
  simp [ofDualMonomial]

@[simp] theorem ofDualMonomial_toDualMonomial (m : CMonomial σ) :
    ofDualMonomial (toDualMonomial m) = m := by
  ext i
  simp [toDualMonomial, ofDualMonomial]

@[simp] theorem toDualMonomial_ofDualMonomial (m : CMonomial σᵒᵈ) :
    toDualMonomial (ofDualMonomial m) = m := by
  ext i
  simp [toDualMonomial, ofDualMonomial]

@[simp] theorem toDualMonomial_single (a : σ) (n : ℕ) :
    toDualMonomial (DFinsupp.single (β := fun _ : σ => ℕ) a n) =
      DFinsupp.single (β := fun _ : σᵒᵈ => ℕ) (OrderDual.toDual a) n := by
  simpa [toDualMonomial] using
    (DFinsupp.comapDomain'_single
      (β := fun _ : σ => ℕ)
      OrderDual.ofDual
      OrderDual.toDual_ofDual
      (k := OrderDual.toDual a)
      (x := n))

@[simp] theorem ofDualMonomial_single (a : σᵒᵈ) (n : ℕ) :
    ofDualMonomial (DFinsupp.single (β := fun _ : σᵒᵈ => ℕ) a n) =
      DFinsupp.single (β := fun _ : σ => ℕ) (OrderDual.ofDual a) n := by
  simpa [ofDualMonomial] using
    (DFinsupp.comapDomain'_single
      (β := fun _ : σᵒᵈ => ℕ)
      OrderDual.toDual
      OrderDual.ofDual_toDual
      (k := OrderDual.ofDual a)
      (x := n))

/-- Additive equivalence from monomials to the graded reverse-lexicographic synonym. -/
def toGrevlex : CMonomial σ ≃+ Grevlex σ where
  toEquiv :=
    { toFun := fun m => toGrlex (toDualMonomial m)
      invFun := fun m => ofDualMonomial (ofGrlex m)
      left_inv := by
        intro m
        simp
      right_inv := by
        intro m
        apply toGrlex_injective
        simp }
  map_add' := by
    intro a b
    simpa [toDualMonomial_add] using
      (toGrlex_add (a := toDualMonomial a) (b := toDualMonomial b))

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ] [WellFoundedLT σ]

set_option backward.isDefEq.respectTransparency false in
/-- The graded reverse lexicographic order on monomials. -/
def grevlex : CMonomialOrder σ where
  syn := Grevlex σ
  acm := by
    unfold Grevlex Grlex
    infer_instance
  lo := by
    unfold Grevlex
    infer_instance
  iocam := by
    unfold Grevlex
    infer_instance
  toSyn := toGrevlex
  toSyn_monotone a b h := by
    change (toGrevlex.toFun a) ≤ (toGrevlex.toFun b)
    change toGrlex (toDualMonomial a) ≤ toGrlex (toDualMonomial b)
    simp only [DFinsupp.Grlex.le_iff]
    have hdual : toDualMonomial a ≤ toDualMonomial b := by
      intro i
      simpa [toDualMonomial] using h (OrderDual.ofDual i)
    by_cases! hdeg :
      CMonomial.degree (σ := σᵒᵈ) (toDualMonomial a) <
        CMonomial.degree (σ := σᵒᵈ) (toDualMonomial b)
    · exact Or.inl hdeg
    · refine Or.inr ⟨le_antisymm ?_ hdeg, DFinsupp.toLex_monotone hdual⟩
      rw [← add_tsub_cancel_of_le hdual]
      simp [CMonomial.degree_add]
  wf := by
    unfold Grevlex
    infer_instance

end CMonomialOrder
