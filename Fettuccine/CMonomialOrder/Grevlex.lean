import Fettuccine.CMonomialOrder
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.DFinsupp.WellFounded

/-!
# The Graded Reverse Lexicographic Order on Monomials

This file provides an implementation of the graded reverse lexicographic order on monomials.
It compares first by total degree, then by colex on variables viewed in `OrderDual`.
-/

def Grevlex (ι : Type*) := ι

variable {ι : Type*}

@[match_pattern] def toGrevlex : ι ≃ Grevlex ι := Equiv.refl _
@[match_pattern] def ofGrevlex : Grevlex ι ≃ ι := Equiv.refl _

@[simp] theorem ofGrevlex_symm_eq : (@ofGrevlex ι).symm = toGrevlex := rfl
@[simp] theorem toGrevlex_symm_eq : (@toGrevlex ι).symm = ofGrevlex := rfl
@[simp] theorem ofGrevlex_toGrevlex (a : ι) : ofGrevlex (toGrevlex a) = a := rfl
@[simp] theorem toGrevlex_ofGrevlex (a : Grevlex ι) : toGrevlex (ofGrevlex a) = a := rfl

theorem ofGrevlex_injective : Function.Injective (ofGrevlex (ι := ι)) :=
  fun _ _ h => h

instance [AddCommMonoid ι] : AddCommMonoid (Grevlex ι) :=
  ofGrevlex.addCommMonoid

theorem toGrevlex_add [AddCommMonoid ι] (a b : ι) :
    toGrevlex (a + b) = toGrevlex a + toGrevlex b := rfl

theorem ofGrevlex_add [AddCommMonoid ι] (a b : Grevlex ι) :
    ofGrevlex (a + b) = ofGrevlex a + ofGrevlex b := rfl

namespace DFinsupp

variable [DecidableEq ι]

/-- Reindex a monomial to the dual variable order. -/
def toDualMonomial : (Π₀ _ : ι, ℕ) → (Π₀ _ : ιᵒᵈ, ℕ) :=
  DFinsupp.comapDomain' OrderDual.ofDual OrderDual.toDual_ofDual

@[simp] theorem toDualMonomial_add (a b : Π₀ _ : ι, ℕ) :
    toDualMonomial (a + b) = toDualMonomial a + toDualMonomial b := by
  ext i
  simp [toDualMonomial]

@[simp] theorem toDualMonomial_single (a : ι) (n : ℕ) :
    toDualMonomial (DFinsupp.single (β := fun _ : ι => ℕ) a n) =
      DFinsupp.single (β := fun _ : ιᵒᵈ => ℕ) (OrderDual.toDual a) n := by
  simpa [toDualMonomial] using
    (DFinsupp.comapDomain'_single
      (β := fun _ : ι => ℕ)
      OrderDual.ofDual
      OrderDual.toDual_ofDual
      (k := OrderDual.toDual a)
      (x := n))

theorem toDualMonomial_monotone : Monotone (toDualMonomial (ι := ι)) := by
  intro a b h
  intro i
  simpa [toDualMonomial] using h (OrderDual.ofDual i)

theorem toDualMonomial_injective : Function.Injective (toDualMonomial (ι := ι)) := by
  intro a b hab
  ext i
  exact congrArg (fun f => f (OrderDual.toDual i)) hab

namespace Grevlex

instance [LT ι] : LT (Grevlex (Π₀ _ : ι, ℕ)) :=
  ⟨fun f g =>
    (toLex
      (CMonomial.degree (σ := ι) (ofGrevlex f),
        toColex (toDualMonomial (ofGrevlex f)))) <
      (toLex
        (CMonomial.degree (σ := ι) (ofGrevlex g),
          toColex (toDualMonomial (ofGrevlex g))))⟩

theorem lt_iff [LT ι] {a b : Grevlex (Π₀ _ : ι, ℕ)} :
    a < b ↔
      CMonomial.degree (σ := ι) (ofGrevlex a) < CMonomial.degree (σ := ι) (ofGrevlex b) ∨
      (CMonomial.degree (σ := ι) (ofGrevlex a) = CMonomial.degree (σ := ι) (ofGrevlex b) ∧
        toColex (toDualMonomial (ofGrevlex a)) <
          toColex (toDualMonomial (ofGrevlex b))) :=
  Prod.Lex.toLex_lt_toLex

variable [LinearOrder ι]

instance isStrictOrder : IsStrictOrder (Grevlex (Π₀ _ : ι, ℕ)) (· < ·) where
  irrefl := fun a => by
    change ¬
      toLex
          (CMonomial.degree (σ := ι) (ofGrevlex a),
            toColex (toDualMonomial (ofGrevlex a))) <
        toLex
          (CMonomial.degree (σ := ι) (ofGrevlex a),
            toColex (toDualMonomial (ofGrevlex a)))
    exact lt_irrefl _
  trans := by
    intro a b c hab hbc
    simp only [lt_iff] at hab hbc ⊢
    rcases hab with (hab | hab)
    · rcases hbc with (hbc | hbc)
      · left; exact lt_trans hab hbc
      · left; exact lt_of_lt_of_eq hab hbc.1
    · rcases hbc with (hbc | hbc)
      · left; exact lt_of_eq_of_lt hab.1 hbc
      · right; exact ⟨Eq.trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩

instance : LinearOrder (Grevlex (Π₀ _ : ι, ℕ)) :=
  LinearOrder.lift'
    (fun f : Grevlex (Π₀ _ : ι, ℕ) =>
      toLex
        (CMonomial.degree (σ := ι) (ofGrevlex f),
          toColex (toDualMonomial (ofGrevlex f))))
    (fun f g hfg => by
      exact ofGrevlex_injective
        (toDualMonomial_injective (toColex.injective (congrArg Prod.snd (toLex.injective hfg)))) )

set_option backward.isDefEq.respectTransparency false in
lemma le_iff {x y : Grevlex (Π₀ _ : ι, ℕ)} :
    x ≤ y ↔
      CMonomial.degree (σ := ι) (ofGrevlex x) < CMonomial.degree (σ := ι) (ofGrevlex y) ∨
      (CMonomial.degree (σ := ι) (ofGrevlex x) = CMonomial.degree (σ := ι) (ofGrevlex y) ∧
        toColex (toDualMonomial (ofGrevlex x)) ≤
          toColex (toDualMonomial (ofGrevlex y))) := by
  simp only [le_iff_eq_or_lt, lt_iff]
  by_cases h : x = y
  · simp [h]
  · have hxy_colex :
      toColex (toDualMonomial (ofGrevlex x)) ≠
        toColex (toDualMonomial (ofGrevlex y)) := by
      intro hxy
      exact h (ofGrevlex_injective (toDualMonomial_injective (toColex.injective hxy)))
    simp [h, hxy_colex]

instance : IsOrderedCancelAddMonoid (Grevlex (Π₀ _ : ι, ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [DFinsupp.Grevlex.le_iff] at h ⊢
    have h' :
        CMonomial.degree (σ := ι) (ofGrevlex a) + CMonomial.degree (σ := ι) (ofGrevlex b) <
            CMonomial.degree (σ := ι) (ofGrevlex a) + CMonomial.degree (σ := ι) (ofGrevlex c) ∨
          (CMonomial.degree (σ := ι) (ofGrevlex a) + CMonomial.degree (σ := ι) (ofGrevlex b) =
              CMonomial.degree (σ := ι) (ofGrevlex a) + CMonomial.degree (σ := ι) (ofGrevlex c) ∧
            toColex (toDualMonomial (ofGrevlex a)) + toColex (toDualMonomial (ofGrevlex b)) ≤
              toColex (toDualMonomial (ofGrevlex a)) + toColex (toDualMonomial (ofGrevlex c))) := by
      simpa [ofGrevlex_add, CMonomial.degree_add, toDualMonomial_add, toColex_add] using h
    rcases h' with hlt | hle
    · exact Or.inl (Nat.add_lt_add_iff_left.mp hlt)
    · refine Or.inr ⟨Nat.add_left_cancel hle.1, ?_⟩
      exact (add_le_add_iff_left _).mp hle.2
  add_le_add_left a b h c := by
    rw [DFinsupp.Grevlex.le_iff] at h ⊢
    rcases h with hlt | hle
    · exact Or.inl (by
        simpa [ofGrevlex_add, CMonomial.degree_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using add_lt_add_left hlt (CMonomial.degree (σ := ι) (ofGrevlex c)))
    · refine Or.inr ⟨by simp [ofGrevlex_add, CMonomial.degree_add, hle.1], ?_⟩
      simpa [ofGrevlex_add, toDualMonomial_add, toColex_add] using
        add_le_add_left hle.2 (toColex (toDualMonomial (ofGrevlex c)))

instance wellFoundedLT [Finite ι] : WellFoundedLT (Grevlex (Π₀ _ : ι, ℕ)) := by
  refine ⟨InvImage.wf
    (fun f : Grevlex (Π₀ _ : ι, ℕ) =>
      (toLex
        (CMonomial.degree (σ := ι) (ofGrevlex f),
          toColex (toDualMonomial (ofGrevlex f))))) ?_⟩
  exact (wellFounded_lt : WellFounded ((· < ·) : ℕ ×ₗ Colex (Π₀ _ : ιᵒᵈ, ℕ) → _))

end Grevlex

end DFinsupp

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ] [Finite σ]

set_option backward.isDefEq.respectTransparency false in
def grevlex : CMonomialOrder σ where
  syn := Grevlex (Π₀ _ : σ, ℕ)
  acm := by
    rw [Grevlex]
    infer_instance
  lo := by infer_instance
  iocam := by infer_instance
  toSyn :=
    { toEquiv := toGrevlex
      map_add' := toGrevlex_add }
  toSyn_monotone a b h := by
    change
      (toLex
          (CMonomial.degree (σ := σ) a,
            toColex (DFinsupp.toDualMonomial (ι := σ) a)) :
        ℕ ×ₗ Colex (Π₀ _ : σᵒᵈ, ℕ)) ≤
      (toLex
          (CMonomial.degree (σ := σ) b,
            toColex (DFinsupp.toDualMonomial (ι := σ) b)) :
        ℕ ×ₗ Colex (Π₀ _ : σᵒᵈ, ℕ))
    apply Prod.Lex.toLex_mono
    refine ⟨?_, ?_⟩
    · rw [← add_tsub_cancel_of_le h]
      simp [CMonomial.degree_add]
    · exact DFinsupp.toColex_monotone (DFinsupp.toDualMonomial_monotone h)
  wf := by infer_instance

end CMonomialOrder
