import Fettuccine.CMonomialOrder
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.DFinsupp.Lex

/-!
# The Graded Lexicographic Order on Monomials

This file provides an implementation of the graded lexicographic order on monomials. For the most
part, the structure of this file largely mirrors the implementation of the "homogeneous
lexicographic order" in Mathlib/Data/Finsupp/MonomialOrder/Grlex.lean.
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

open scoped Function in
/-- `DFinsupp r s` is the graded lexicographic order on `Π₀ _ : ι, ℕ`, where `ι` is ordered by `r`
    and `ℕ` is ordered by `s`. The type synonym `Grlex (Π₀ _ : ι, ℕ)` has an order given by
    `DFinsupp.Grlex`. -/
protected def Grlex (r : ι → ι → Prop) (s : ℕ → ℕ → Prop) :
    (Π₀ _ : ι, ℕ) → (Π₀ _ : ι, ℕ) → Prop :=
  (Prod.Lex s (DFinsupp.Lex r (fun _ ↦ s))) on (fun x ↦ (0, x))

theorem grlex_def {r : ι → ι → Prop} {s : ℕ → ℕ → Prop} {a b : Π₀ _ : ι, ℕ} :
    DFinsupp.Grlex r s a b ↔ Prod.Lex s (DFinsupp.Lex r (fun _ ↦ s)) (0, a) (0, b) :=
  Iff.rfl

namespace Grlex

theorem wf
    {r : ι → ι → Prop} [Std.Trichotomous r] (hr : WellFounded (Function.swap r))
    {s : ℕ → ℕ → Prop} {hs : WellFounded s} (hs₀ : ∀ n, ¬ s n 0) :
    WellFounded (DFinsupp.Grlex r s) := by
  sorry

end Grlex

end DFinsupp
