import Fettuccine.CMonomialOrder
import Fettuccine.Algorithm.FMonomialOrder
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.DFinsupp.Lex

/-!
# The Graded Lexicographic Order on Monomials

This file provides an implementation of the graded lexicographic order on monomials. For the most
part, the structure of this file largely mirrors the implementation of the "homogeneous"
lexicographic order in Mathlib/Data/Finsupp/CMonomialOrder/DegLex.lean.

## Definitions

* `Grlex ι` : a type synonym used to equip a type with the graded lexicographic order.
* `CMonomialOrder.grlex` : the graded lexicographic monomial order on `CMonomial σ`.

## Theorems

* `CMonomialOrder.grlex.IsGraded` : the graded lexicographic order is graded.
-/

/-- A type synonym to equip a type with its graded lexicographic order. -/
def Grlex (ι : Type*) := ι

variable {ι : Type*}

/-- `toGrlex` is the identity function to the `Grlex` of a type. -/
@[match_pattern] def toGrlex : ι ≃ Grlex ι := Equiv.refl _

theorem toGrlex_injective : Function.Injective (toGrlex (ι := ι)) :=
  fun _ _ ↦ _root_.id

theorem toGrlex_inj {a b : ι} : toGrlex a = toGrlex b ↔ a = b := Iff.rfl

/-- `ofGrlex` is the identity function from the `Grlex` of a type. -/
@[match_pattern] def ofGrlex : Grlex ι ≃ ι := Equiv.refl _

theorem ofGrlex_injective : Function.Injective (ofGrlex (ι := ι)) :=
  fun _ _ ↦ _root_.id

theorem ofGrlex_inj {a b : Grlex ι} : ofGrlex a = ofGrlex b ↔ a = b := Iff.rfl

@[simp] theorem ofGrlex_symm_eq : (@ofGrlex ι).symm = toGrlex := rfl

@[simp] theorem toGrlex_symm_eq : (@toGrlex ι).symm = ofGrlex := rfl

@[simp] theorem ofGrlex_toGrlex (a : ι) : ofGrlex (toGrlex a) = a := rfl

@[simp] theorem toGrlex_ofGrlex (a : Grlex ι) : toGrlex (ofGrlex a) = a := rfl

/-- A recursor for `Grlex`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def Grlex.rec {β : Grlex ι → Sort*} (h : ∀ a, β (toGrlex a)) :
    ∀ a, β a := fun a => h (ofGrlex a)

@[simp] lemma Grlex.forall_iff {p : Grlex ι → Prop} : (∀ a, p a) ↔ ∀ a, p (toGrlex a) := Iff.rfl
@[simp] lemma Grlex.exists_iff {p : Grlex ι → Prop} : (∃ a, p a) ↔ ∃ a, p (toGrlex a) := Iff.rfl

instance [AddCommMonoid ι] : AddCommMonoid (Grlex ι) :=
  ofGrlex.addCommMonoid

theorem toGrlex_add [AddCommMonoid ι] (a b : ι) :
    toGrlex (a + b) = toGrlex a + toGrlex b := rfl

theorem ofGrlex_add [AddCommMonoid ι] (a b : Grlex ι) :
    ofGrlex (a + b) = ofGrlex a + ofGrlex b := rfl

namespace DFinsupp

variable [DecidableEq ι]

open scoped Function in
/-- `DFinsupp r s` is the graded lexicographic order on `Π₀ _ : ι, ℕ`, where `ι` is ordered by `r`
    and `ℕ` is ordered by `s`. The type synonym `Grlex (Π₀ _ : ι, ℕ)` has an order given by
    `DFinsupp.Grlex`. -/
protected def Grlex (r : ι → ι → Prop) (s : ℕ → ℕ → Prop) :
    (Π₀ _ : ι, ℕ) → (Π₀ _ : ι, ℕ) → Prop :=
  (Prod.Lex s (DFinsupp.Lex r (fun _ ↦ s))) on
    (fun x ↦ (CMonomial.degree (σ := ι) x, x))

theorem grlex_def {r : ι → ι → Prop} {s : ℕ → ℕ → Prop} {a b : Π₀ _ : ι, ℕ} :
    DFinsupp.Grlex r s a b ↔
      Prod.Lex s (DFinsupp.Lex r (fun _ ↦ s))
        (CMonomial.degree (σ := ι) a, a) (CMonomial.degree (σ := ι) b, b) :=
  Iff.rfl

namespace Grlex

theorem wf
    {r : ι → ι → Prop} [Std.Trichotomous r] (hr : WellFounded (Function.swap r))
    {s : ℕ → ℕ → Prop} (hs : WellFounded s) (hs₀ : ∀ n, ¬ s n 0) :
    WellFounded (DFinsupp.Grlex r s) := by
  have wft := WellFounded.prod_lex hs
    (DFinsupp.Lex.wellFounded' (fun {_} a ↦ hs₀ a) (fun _ ↦ hs) hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold DFinsupp.Grlex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ ↦ trivial)

instance [LT ι] : LT (Grlex (Π₀ _ : ι, ℕ)) :=
  ⟨fun f g ↦ DFinsupp.Grlex (· < ·) (· < ·) (ofGrlex f) (ofGrlex g)⟩

theorem lt_def [LT ι] {a b : Grlex (Π₀ _ : ι, ℕ)} :
    a < b ↔
      (toLex (CMonomial.degree (σ := ι) (ofGrlex a), toLex (ofGrlex a))) <
        (toLex (CMonomial.degree (σ := ι) (ofGrlex b), toLex (ofGrlex b))) :=
  Iff.rfl

theorem lt_iff [LT ι] {a b : Grlex (Π₀ _ : ι, ℕ)} :
    a < b ↔
      CMonomial.degree (σ := ι) (ofGrlex a) < CMonomial.degree (σ := ι) (ofGrlex b) ∨
      (CMonomial.degree (σ := ι) (ofGrlex a) = CMonomial.degree (σ := ι) (ofGrlex b) ∧
        toLex (ofGrlex a) < toLex (ofGrlex b)) := by
  simp [lt_def, Prod.Lex.toLex_lt_toLex]

variable [LinearOrder ι]

instance isStrictOrder : IsStrictOrder (Grlex (Π₀ _ : ι, ℕ)) (· < ·) where
  irrefl := fun a ↦ by
    change ¬
      toLex (CMonomial.degree (σ := ι) (ofGrlex a), toLex (ofGrlex a)) <
        toLex (CMonomial.degree (σ := ι) (ofGrlex a), toLex (ofGrlex a))
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

/-- The linear order on `DFinsupp`s obtained by the graded lexicographic ordering. -/
instance : LinearOrder (Grlex (Π₀ _ : ι, ℕ)) :=
  LinearOrder.lift'
    (fun f : Grlex (Π₀ _ : ι, ℕ) ↦
      toLex (CMonomial.degree (σ := ι) (ofGrlex f), toLex (ofGrlex f)))
    (fun f g hfg ↦ by
      apply ofGrlex_injective
      apply toLex.injective
      exact congrArg Prod.snd (toLex.injective hfg))

set_option backward.isDefEq.respectTransparency false in
theorem le_iff {x y : Grlex (Π₀ _ : ι, ℕ)} :
    x ≤ y ↔
      CMonomial.degree (σ := ι) (ofGrlex x) < CMonomial.degree (σ := ι) (ofGrlex y) ∨
      (CMonomial.degree (σ := ι) (ofGrlex x) = CMonomial.degree (σ := ι) (ofGrlex y) ∧
        toLex (ofGrlex x) ≤ toLex (ofGrlex y)) := by
  simp only [le_iff_eq_or_lt, lt_iff]
  by_cases h : x = y
  · simp [h]
  · have hxy_lex : toLex (ofGrlex x) ≠ toLex (ofGrlex y) := by
      intro hxy
      exact h (ofGrlex_injective (toLex.injective hxy))
    simp [h, hxy_lex]

instance : IsOrderedCancelAddMonoid (Grlex (Π₀ _ : ι, ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [DFinsupp.Grlex.le_iff] at h ⊢
    simpa only [ofGrlex_add, CMonomial.degree_add, map_add, toLex_add, add_lt_add_iff_left,
      add_right_inj, add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [DFinsupp.Grlex.le_iff] at h ⊢
    simpa [ofGrlex_add, CMonomial.degree_add, map_add, toLex_add] using h

set_option backward.isDefEq.respectTransparency false in
theorem single_strictAnti : StrictAnti (fun (a : ι) ↦
    toGrlex (DFinsupp.single (β := fun _ : ι => ℕ) a 1)) := by
  intro a b h
  rw [DFinsupp.Grlex.lt_iff]
  refine Or.inr ⟨?_, ?_⟩
  · simp [CMonomial.degree, DFinsupp.support_single_ne_zero]
  · rw [DFinsupp.Lex.lt_iff]
    refine ⟨a, ?_, ?_⟩
    · intro j hj
      have hja : j ≠ a := ne_of_lt hj
      have hjb : j ≠ b := ne_of_lt (lt_trans hj h)
      simp [DFinsupp.single_eq_of_ne hja, DFinsupp.single_eq_of_ne hjb]
    · simp [DFinsupp.single_eq_of_ne (ne_of_lt h)]

theorem single_antitone : Antitone (fun (a : ι) ↦ toGrlex (DFinsupp.single a 1)) :=
  single_strictAnti.antitone

theorem single_lt_iff {a b : ι} :
    toGrlex (DFinsupp.single (β := fun _ : ι => ℕ) b 1) <
      toGrlex (DFinsupp.single (β := fun _ : ι => ℕ) a 1) ↔ a < b :=
  single_strictAnti.lt_iff_gt

theorem single_le_iff {a b : ι} :
    toGrlex (DFinsupp.single (β := fun _ : ι => ℕ) b 1) ≤
      toGrlex (DFinsupp.single (β := fun _ : ι => ℕ) a 1) ↔ a ≤ b :=
  single_strictAnti.le_iff_ge

theorem monotone_degree :
    Monotone (fun x : Grlex (Π₀ _ : ι, ℕ) ↦ CMonomial.degree (σ := ι) (ofGrlex x)) := by
  intro x y
  rw [DFinsupp.Grlex.le_iff]
  rintro (h | h)
  · exact le_of_lt h
  · exact le_of_eq h.1

instance orderBot : OrderBot (Grlex (Π₀ _ : ι, ℕ)) where
  bot := toGrlex (0 : Π₀ _ : ι, ℕ)
  bot_le x := by
    rw [DFinsupp.Grlex.le_iff]
    by_cases hdeg : 0 < CMonomial.degree (σ := ι) (ofGrlex x)
    · exact Or.inl (by simpa [ofGrlex_toGrlex] using hdeg)
    · refine Or.inr ⟨?_, ?_⟩
      · have hzero : CMonomial.degree (σ := ι) (ofGrlex x) = 0 := Nat.eq_zero_of_not_pos hdeg
        simpa [ofGrlex_toGrlex] using hzero.symm
      · simpa [ofGrlex_toGrlex] using
          (DFinsupp.toLex_monotone (show (0 : Π₀ _ : ι, ℕ) ≤ ofGrlex x from
            fun _ => Nat.zero_le _))

instance wellFoundedLT [WellFoundedGT ι] : WellFoundedLT (Grlex (Π₀ _ : ι, ℕ)) :=
  ⟨wf wellFounded_gt wellFounded_lt fun n => (Nat.not_lt_zero n)⟩

end Grlex

end DFinsupp

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ] [WellFoundedGT σ]

set_option backward.isDefEq.respectTransparency false in
/-- The graded lexicographic order on monomials. -/
def grlex : CMonomialOrder σ where
  syn := Grlex (Π₀ _ : σ, ℕ)
  acm := by
    rw [Grlex]
    infer_instance
  lo := by infer_instance
  iocam := by infer_instance
  toSyn :=
    { toEquiv := toGrlex
      map_add' := toGrlex_add }
  toSyn_monotone a b h := by
    simp only [DFinsupp.Grlex.le_iff]
    by_cases! ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ ha, DFinsupp.toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h]
      simp [CMonomial.degree_add]
  wf := by infer_instance

theorem grlex_le_iff {a b : CMonomial σ} :
    a ≼[grlex] b ↔ toGrlex a ≤ toGrlex b := by
  rfl

theorem grlex_lt_iff {a b : CMonomial σ} :
    a ≺[grlex] b ↔ toGrlex a < toGrlex b := by
  rfl

theorem grlex_single_le_iff {a b : σ} :
    DFinsupp.single (β := fun _ : σ => ℕ) a 1 ≼[grlex]
      DFinsupp.single (β := fun _ : σ => ℕ) b 1 ↔ b ≤ a := by
  rw [grlex_le_iff, DFinsupp.Grlex.single_le_iff]

theorem grlex_single_lt_iff {a b : σ} :
    DFinsupp.single (β := fun _ : σ => ℕ) a 1 ≺[grlex]
      DFinsupp.single (β := fun _ : σ => ℕ) b 1 ↔ b < a := by
  rw [grlex_lt_iff, DFinsupp.Grlex.single_lt_iff]

theorem grlex.IsGraded : (grlex (σ := σ)).IsGraded := by
  intro m₁ m₂ hdeg
  rw [grlex_lt_iff]
  exact (DFinsupp.Grlex.lt_iff (a := toGrlex m₁) (b := toGrlex m₂)).mpr
    (Or.inl (by simpa using hdeg))

/-- Type-level tag for graded lexicographic monomial order. -/
inductive GrlexOrder : Type where
  | mk

instance grlexOrderTag : CMonomialOrderTag GrlexOrder σ where
  ord := grlex

instance grlexFastOrderTag (n : ℕ) : FMonomialOrderTag GrlexOrder n where
  ord := FMonomialOrder.grlex

end CMonomialOrder
