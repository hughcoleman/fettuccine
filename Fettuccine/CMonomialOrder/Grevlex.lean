import Fettuccine.CMonomialOrder
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.DFinsupp.Lex

/-!
# The Graded Reverse Lexicographic Order on Monomials

This file provides an implementation of the graded reverse lexicographic order on monomials.

## Definitions

* `Grevlex ι` : a type synonym used to equip a type with the graded reverse lexicographic order.
* `CMonomialOrder.grevlex` : the graded reverse lexicographic monomial order on `CMonomial σ`.

## Theorems

* `CMonomialOrder.grevlex.IsGraded` : the graded reverse lexicographic order is graded.
-/

/-- A type synonym to equip a type with its graded reverse lexicographic order. -/
def Grevlex (ι : Type*) := ι

variable {ι : Type*}

/-- `toGrevlex` is the identity function to the `Grevlex` of a type. -/
@[match_pattern] def toGrevlex : ι ≃ Grevlex ι := Equiv.refl _

theorem toGrevlex_injective : Function.Injective (toGrevlex (ι := ι)) :=
  fun _ _ => _root_.id

theorem toGrevlex_inj {a b : ι} : toGrevlex a = toGrevlex b ↔ a = b := Iff.rfl

/-- `ofGrevlex` is the identity function from the `Grevlex` of a type. -/
@[match_pattern] def ofGrevlex : Grevlex ι ≃ ι := Equiv.refl _

theorem ofGrevlex_injective : Function.Injective (ofGrevlex (ι := ι)) :=
  fun _ _ => _root_.id

theorem ofGrevlex_inj {a b : Grevlex ι} : ofGrevlex a = ofGrevlex b ↔ a = b := Iff.rfl

@[simp] theorem ofGrevlex_symm_eq : (@ofGrevlex ι).symm = toGrevlex := rfl

@[simp] theorem toGrevlex_symm_eq : (@toGrevlex ι).symm = ofGrevlex := rfl

@[simp] theorem ofGrevlex_toGrevlex (a : ι) : ofGrevlex (toGrevlex a) = a := rfl

@[simp] theorem toGrevlex_ofGrevlex (a : Grevlex ι) : toGrevlex (ofGrevlex a) = a := rfl

/-- A recursor for `Grevlex`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def Grevlex.rec {β : Grevlex ι → Sort*} (h : ∀ a, β (toGrevlex a)) :
    ∀ a, β a := fun a => h (ofGrevlex a)

@[simp] lemma Grevlex.forall_iff {p : Grevlex ι → Prop} : (∀ a, p a) ↔ ∀ a, p (toGrevlex a) :=
  Iff.rfl

@[simp] lemma Grevlex.exists_iff {p : Grevlex ι → Prop} : (∃ a, p a) ↔ ∃ a, p (toGrevlex a) :=
  Iff.rfl

instance [AddCommMonoid ι] : AddCommMonoid (Grevlex ι) :=
  ofGrevlex.addCommMonoid

theorem toGrevlex_add [AddCommMonoid ι] (a b : ι) :
    toGrevlex (a + b) = toGrevlex a + toGrevlex b := rfl

theorem ofGrevlex_add [AddCommMonoid ι] (a b : Grevlex ι) :
    ofGrevlex (a + b) = ofGrevlex a + ofGrevlex b := rfl

namespace DFinsupp

variable [DecidableEq ι]

open scoped Function in
/-- `DFinsupp.Grevlex r s` is the graded reverse lexicographic relation on `Π₀ _ : ι, ℕ`.
The tie-breaker is the colexicographic relation induced by `r` on equal total degree. -/
protected def Grevlex (r : ι → ι → Prop) (s : ℕ → ℕ → Prop) :
    (Π₀ _ : ι, ℕ) → (Π₀ _ : ι, ℕ) → Prop :=
  (Prod.Lex s (DFinsupp.Lex r (fun _ => s))) on (fun x => (CMonomial.degree (σ := ι) x, x))

theorem grevlex_def {r : ι → ι → Prop} {s : ℕ → ℕ → Prop} {a b : Π₀ _ : ι, ℕ} :
    DFinsupp.Grevlex r s a b ↔
      Prod.Lex s (DFinsupp.Lex r (fun _ => s))
        (CMonomial.degree (σ := ι) a, a) (CMonomial.degree (σ := ι) b, b) :=
  Iff.rfl

namespace Grevlex

theorem wf [Finite ι] {r : ι → ι → Prop} [IsStrictTotalOrder ι r]
    {s : ℕ → ℕ → Prop} (hs : WellFounded s) :
    WellFounded (DFinsupp.Grevlex r s) := by
  have wft := WellFounded.prod_lex hs
    (DFinsupp.Lex.wellFounded_of_finite (r := r) (s := fun _ : ι => s) (fun _ => hs))
  rw [← Set.wellFoundedOn_univ] at wft
  unfold DFinsupp.Grevlex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ => trivial)

instance [LT ι] : LT (Grevlex (Π₀ _ : ι, ℕ)) :=
  ⟨fun f g => DFinsupp.Grevlex (· > ·) (· < ·) (ofGrevlex f) (ofGrevlex g)⟩

theorem lt_def [LT ι] {a b : Grevlex (Π₀ _ : ι, ℕ)} :
    a < b ↔
      (toLex (CMonomial.degree (σ := ι) (ofGrevlex a), toColex (ofGrevlex a))) <
        (toLex (CMonomial.degree (σ := ι) (ofGrevlex b), toColex (ofGrevlex b))) :=
  Iff.rfl

theorem lt_iff [LT ι] {a b : Grevlex (Π₀ _ : ι, ℕ)} :
    a < b ↔
      CMonomial.degree (σ := ι) (ofGrevlex a) < CMonomial.degree (σ := ι) (ofGrevlex b) ∨
      (CMonomial.degree (σ := ι) (ofGrevlex a) = CMonomial.degree (σ := ι) (ofGrevlex b) ∧
        toColex (ofGrevlex a) < toColex (ofGrevlex b)) := by
  simp [lt_def, Prod.Lex.toLex_lt_toLex]

variable [LinearOrder ι]

instance isStrictOrder : IsStrictOrder (Grevlex (Π₀ _ : ι, ℕ)) (· < ·) where
  irrefl := fun a => by
    change ¬
      toLex (CMonomial.degree (σ := ι) (ofGrevlex a), toColex (ofGrevlex a)) <
        toLex (CMonomial.degree (σ := ι) (ofGrevlex a), toColex (ofGrevlex a))
    exact lt_irrefl _
  trans := by
    intro a b c hab hbc
    simp only [lt_iff] at hab hbc ⊢
    rcases hab with hab | hab
    · rcases hbc with hbc | hbc
      · exact Or.inl (lt_trans hab hbc)
      · exact Or.inl (lt_of_lt_of_eq hab hbc.1)
    · rcases hbc with hbc | hbc
      · exact Or.inl (lt_of_eq_of_lt hab.1 hbc)
      · exact Or.inr ⟨Eq.trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩

/-- The linear order on `DFinsupp`s obtained by the graded reverse lexicographic ordering. -/
instance : LinearOrder (Grevlex (Π₀ _ : ι, ℕ)) :=
  LinearOrder.lift'
    (fun f : Grevlex (Π₀ _ : ι, ℕ) =>
      toLex (CMonomial.degree (σ := ι) (ofGrevlex f), toColex (ofGrevlex f)))
    (fun f g hfg => by
      apply ofGrevlex_injective
      exact toColex.injective (congrArg Prod.snd (toLex.injective hfg)))

set_option backward.isDefEq.respectTransparency false in
theorem le_iff {x y : Grevlex (Π₀ _ : ι, ℕ)} :
    x ≤ y ↔
      CMonomial.degree (σ := ι) (ofGrevlex x) < CMonomial.degree (σ := ι) (ofGrevlex y) ∨
      (CMonomial.degree (σ := ι) (ofGrevlex x) = CMonomial.degree (σ := ι) (ofGrevlex y) ∧
        toColex (ofGrevlex x) ≤ toColex (ofGrevlex y)) := by
  simp only [le_iff_eq_or_lt, lt_iff]
  by_cases h : x = y
  · simp [h]
  · have hxy_colex : toColex (ofGrevlex x) ≠ toColex (ofGrevlex y) := by
      intro hxy
      exact h (ofGrevlex_injective (toColex.injective hxy))
    simp [h, hxy_colex]

instance : IsOrderedCancelAddMonoid (Grevlex (Π₀ _ : ι, ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [DFinsupp.Grevlex.le_iff] at h ⊢
    simpa only [ofGrevlex_add, CMonomial.degree_add, map_add, toColex_add,
      add_lt_add_iff_left, add_right_inj, add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [DFinsupp.Grevlex.le_iff] at h ⊢
    simpa [ofGrevlex_add, CMonomial.degree_add, map_add, toColex_add] using h

theorem monotone_degree :
    Monotone (fun x : Grevlex (Π₀ _ : ι, ℕ) => CMonomial.degree (σ := ι) (ofGrevlex x)) := by
  intro x y
  rw [DFinsupp.Grevlex.le_iff]
  rintro (h | h)
  · exact le_of_lt h
  · exact le_of_eq h.1

instance wellFoundedLT [Finite ι] : WellFoundedLT (Grevlex (Π₀ _ : ι, ℕ)) :=
  ⟨wf (r := (· > ·)) (hs := wellFounded_lt)⟩

end Grevlex

end DFinsupp

namespace CMonomialOrder

variable {σ : Type*} [DecidableEq σ] [LinearOrder σ] [Finite σ]

set_option backward.isDefEq.respectTransparency false in
/-- The graded reverse lexicographic order on monomials. -/
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
    simp only [DFinsupp.Grevlex.le_iff]
    by_cases! ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ ha, DFinsupp.toColex_monotone h⟩
      rw [← add_tsub_cancel_of_le h]
      simp [CMonomial.degree_add]
  wf := by infer_instance

theorem grevlex_le_iff {a b : CMonomial σ} :
    a ≼[grevlex] b ↔ toGrevlex a ≤ toGrevlex b := by
  rfl

theorem grevlex_lt_iff {a b : CMonomial σ} :
    a ≺[grevlex] b ↔ toGrevlex a < toGrevlex b := by
  rfl

theorem grevlex.IsGraded : (grevlex (σ := σ)).IsGraded := by
  intro m₁ m₂ hdeg
  rw [grevlex_lt_iff]
  exact (DFinsupp.Grevlex.lt_iff (a := toGrevlex m₁) (b := toGrevlex m₂)).mpr
    (Or.inl (by simpa using hdeg))

end CMonomialOrder
