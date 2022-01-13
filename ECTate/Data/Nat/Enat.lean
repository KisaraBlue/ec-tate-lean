import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Order
import Mathlib.Algebra.Ring.Basic
import Mathlib.Init.Data.Nat.Lemmas

inductive Enat where
  | ofN : ℕ → Enat
  | top : Enat

notation "ℕ∪∞" => Enat
notation "∞" => Enat.top

namespace Enat

def succ : ℕ∪∞ → ℕ∪∞
  | ofN a => ofN (Nat.succ a)
  | ∞ => ∞

def add : ℕ∪∞ → ℕ∪∞ → ℕ∪∞
  | a, ∞ => ∞
  | ∞, a => ∞
  | ofN a, ofN b => ofN (a + b)

instance : Add ℕ∪∞ where
  add := add

inductive le : ℕ∪∞ → ℕ∪∞ → Prop
  | in_nat {n m : Nat} : Nat.le n m → le (ofN n) (ofN m)
  | below_top          : le n ∞

instance : LE ℕ∪∞ where
  le := le

def lt (n m : ℕ∪∞) : Prop :=
  n ≠ ∞ ∧ le (succ n) m

instance : LT ℕ∪∞ where
  lt := lt

@[simp] theorem succ_ofN (a : Nat) : succ (ofN a) = ofN a.succ := rfl

@[simp] theorem add_ofN (a b : Nat) : ofN a + ofN b = ofN (a + b) := rfl
@[simp] theorem add_top (a : ℕ∪∞) : a + ∞ = ∞ := by
  cases a
  . rfl
  . rfl
@[simp] theorem top_add (a : ℕ∪∞) : ∞ + a = ∞ := by
  cases a
  . rfl
  . rfl

theorem lt_top (n : ℕ) : LT.lt (ofN n) ∞ := by
  exact And.intro (Enat.noConfusion) (le.below_top)

theorem succ_pos (n : ℕ∪∞) : LT.lt (ofN 0) (succ n) := by
  cases n with
  | ofN n =>
    exact And.intro (Enat.noConfusion) (by rw [succ_ofN 0, succ_ofN n]; exact le.in_nat (Nat.succ_le_succ (Nat.zero_le n)))
  | top => exact lt_top 0

theorem le_refl (n : ℕ∪∞) : LE.le n n := by
  cases n with
  | ofN n => exact le.in_nat (Nat.le_refl n)
  | top     => exact le.below_top

theorem le_trans {n m k : ℕ∪∞} : LE.le n m → LE.le m k → LE.le n k
  | le.in_nat h, le.in_nat h' => le.in_nat (Nat.le_trans h h')
  | _, le.below_top                 => le.below_top

theorem le_succ (n : ℕ∪∞) : LE.le n (succ n) := by
  cases n with
  | ofN n => exact le.in_nat (Nat.le_succ n)
  | top     => exact le.below_top

theorem le_of_succ_le {n m : ℕ∪∞} (h : succ n ≤ m) : n ≤ m :=
  le_trans (le_succ n) h

theorem le_of_lt {n m : ℕ∪∞} (h : n < m) : n ≤ m := by
  cases m with
  | ofN m =>
    cases n with
    | ofN n => exact le_of_succ_le h.right
    | top =>
      apply False.elim
      apply h.left
      rfl
  | top    => exact le.below_top

theorem lt_or_ge (n m : ℕ∪∞) : Or (LT.lt n m) (GE.ge n m) := by
  cases n with
  | top     => exact Or.inr (le.below_top)
  | ofN n =>
    cases m with
    | top     => exact Or.inl (And.intro Enat.noConfusion le.below_top)
    | ofN m =>
      cases Nat.lt_or_ge n m with
      | inl h =>
        exact Or.inl (And.intro Enat.noConfusion (le.in_nat h))
      | inr h =>
        exact Or.inr (le.in_nat h)

theorem not_le_of_gt {n m : ℕ∪∞} (h : n > m) : ¬ n ≤ m := by
  cases m with
  | top     =>
    intro _
    apply h.left
    rfl
  | ofN m =>
    cases n with
    | top =>
      intro absurd
      cases absurd
    | ofN n =>
      intro nlem
      cases h.right with
      | in_nat nat_le =>
        apply Nat.not_le_of_gt nat_le
        cases nlem
        assumption

theorem gt_of_not_le {n m : ℕ∪∞} (h : ¬ n ≤ m) : n > m :=
  match lt_or_ge m n with
  | Or.inl h₁ => h₁
  | Or.inr h₁ => absurd h₁ h

lemma lt_iff_le_not_le {m n : ℕ∪∞} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
⟨fun h => ⟨le_of_lt h, not_le_of_gt h⟩, fun h => gt_of_not_le h.2⟩

theorem le_antisymm {n m : ℕ∪∞} (h1 : LE.le n m) (h2 : LE.le m n) : Eq n m := by
  cases n with
  | top =>
    cases h1
    rfl
  | ofN n =>
    cases m with
    | top => cases h2
    | ofN m =>
      cases h1 with
      | in_nat h1 =>
        cases h2 with
        | in_nat h2 =>
          exact congrArg ofN (Nat.le_antisymm h1 h2)

theorem le_total (m n : ℕ∪∞) : m ≤ n ∨ n ≤ m :=
  match lt_or_ge m n with
  | Or.inl h => Or.inl (le_of_lt h)
  | Or.inr h => Or.inr h

lemma le_ofN (m n : Nat) : m ≤ n ↔ ofN m ≤ ofN n := by
  apply Iff.intro
  intro h
  exact le.in_nat h
  intro h
  cases h
  assumption

theorem lt_ofN (m n : ℕ) : m < n ↔ ofN m < ofN n := by
  apply Iff.intro
  intro h
  exact And.intro (Enat.noConfusion) (by rw [succ_ofN]; exact le.in_nat h)
  intro h
  cases h.right
  assumption

lemma eq_ofN (m n : Nat) : m = n ↔ ofN m = ofN n := by
  apply Iff.intro
  intro h
  exact congrArg ofN h
  intro h
  cases h
  rfl

instance : DecidableRel ((. ≤ . ) : ℕ∪∞ → ℕ∪∞ → Prop) := fun n m =>
match n, m with
  | ofN b, ofN c =>
  decidable_of_decidable_of_iff inferInstance (le_ofN b c)
  | _, ∞         => isTrue le.below_top
  | ∞, ofN a     => isFalse (fun h => by cases h)

instance : DecidableRel ((. = . ) : ℕ∪∞ → ℕ∪∞ → Prop) := fun n m =>
match n, m with
  | ofN b, ofN c =>
  decidable_of_decidable_of_iff inferInstance (eq_ofN b c)
  | ∞, ∞         => isTrue rfl
  | ∞, ofN a     => isFalse (fun h => by cases h)
  | ofN a, ∞     => isFalse (fun h => by cases h)

instance : DecidableRel ((. < . ) : ℕ∪∞ → ℕ∪∞ → Prop) := by sorry


theorem eq_zero_or_pos : ∀ (n : ℕ∪∞), n = ofN 0 ∨ n > ofN 0
  | ofN 0   => Or.inl rfl
  | ofN (Nat.succ n) => by rw [←succ_ofN n]; exact Or.inr (succ_pos _)
  | ∞ => Or.inr (lt_top 0)

lemma pos_of_ne_zero {n : ℕ∪∞} : n ≠ ofN 0 → ofN 0 < n :=
Or.resolve_left (eq_zero_or_pos n)

instance : LinearOrder ℕ∪∞ :=
{ le               := le,
  le_refl          := le_refl,
  le_trans         := @le_trans,
  le_antisymm      := @le_antisymm,
  le_total         := @le_total,
  lt               := lt,
  lt_iff_le_not_le := @lt_iff_le_not_le,
  decidable_lt     := inferInstance,
  decidable_le     := inferInstance,
  decidable_eq     := inferInstance }

instance : AddCommMonoid ℕ∪∞ :=
{ add_assoc   := by sorry,
  zero        := ofN Nat.zero,
  add_zero    := by sorry,
  zero_add    := by sorry,
  nsmul_zero' := by sorry,
  nsmul_succ' := by sorry,
  add_comm    := by sorry }

end Enat
