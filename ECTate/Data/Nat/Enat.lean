import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Algebra.Ring.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Util.WhatsNew -- TODO remove
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NormCast
import Aesop

inductive Enat where
  | ofN : ℕ → Enat
  | top : Enat
deriving Repr, DecidableEq

notation "ℕ∪∞" => Enat
notation "∞" => Enat.top

namespace Enat

def succ : ℕ∪∞ → ℕ∪∞
  | ofN a => ofN (Nat.succ a)
  | ∞ => ∞

@[simp]
lemma succ_top : succ ∞ = ∞ := rfl

protected def add : ℕ∪∞ → ℕ∪∞ → ℕ∪∞
  | _, ∞ => ∞
  | ∞, _ => ∞
  | ofN a, ofN b => ofN (a + b)

instance : Add ℕ∪∞ where
  add := Enat.add

protected inductive le : ℕ∪∞ → ℕ∪∞ → Prop
  | in_nat {n m : Nat} : Nat.le n m → Enat.le (ofN n) (ofN m)
  | below_top          : Enat.le n ∞

instance : LE ℕ∪∞ where
  le := Enat.le

protected def lt (n m : ℕ∪∞) : Prop :=
  n ≠ ∞ ∧ Enat.le (succ n) m

instance : LT ℕ∪∞ where
  lt := Enat.lt

theorem succ_ofN (a : Nat) : succ (ofN a) = ofN a.succ := rfl

@[simp] theorem add_ofN (a b : Nat) : ofN a + ofN b = ofN (a + b) := rfl

@[simp] theorem add_top (a : ℕ∪∞) : a + ∞ = ∞ := match a with
  | top => rfl
  | ofN _ => rfl
@[simp] theorem top_add (a : ℕ∪∞) : ∞ + a = ∞ := match a with
  | top => rfl
  | ofN _ => rfl

protected theorem add_assoc (a b c : ℕ∪∞) : a + b + c = a + (b + c) := by
  cases a with
  | top => simp
  | ofN a => cases b with
    | top => simp
    | ofN b => cases c with
      | top => simp
      | ofN c => simp [Nat.add_assoc]

protected theorem add_zero (a : ℕ∪∞) : a + ofN 0 = a := by
  match a with
  | top => exact top_add (ofN 0)
  | ofN a => simp

protected theorem zero_add (a : ℕ∪∞) : ofN 0 + a = a := by
  match a with
  | top => exact add_top (ofN 0)
  | ofN a => simp

-- theorem nsmul_zero' (x : ℕ∪∞) : nsmul_rec 0 x = ofN 0 := by
--   simp [nsmul_rec]
--   rfl

-- theorem nsmul_succ' (n : ℕ) (x : ℕ∪∞) : nsmul_rec (Nat.succ n) x = x + nsmul_rec n x := by
--   induction n with
--   | zero =>
--     simp [nsmul_rec, nsmul_zero']
--   | succ n ih =>
--     simp [nsmul_rec]


protected theorem add_comm (a b : ℕ∪∞) : a + b = b + a := by
  cases a with
  | top => simp
  | ofN a => cases b with
    | top => simp
    | ofN b =>
      simp [add_ofN]
      exact Nat.add_comm a b

instance : AddMonoid ℕ∪∞ :=
{ add_assoc   := Enat.add_assoc,
  zero        := ofN Nat.zero,
  add_zero    := Enat.add_zero,
  zero_add    := Enat.zero_add }

instance : AddCommMonoid ℕ∪∞ :=
{ inferInstanceAs (AddMonoid Enat) with
  add_comm    := Enat.add_comm }

protected def one := ofN 1

instance : AddMonoidWithOne ℕ∪∞ :=
{ inferInstanceAs (AddMonoid Enat) with
  one    := Enat.one
  natCast := ofN
  natCast_zero := rfl
  natCast_succ := fun _ => rfl }

@[simp]
theorem succ_ofNat (a : Nat) : succ a = a.succ := rfl
@[simp]
theorem succ_zero : succ 0 = 1 := rfl

theorem add_ofNat (a b : Nat) : a + b = (↑(a + b) : Enat) := rfl

theorem ofN_inj : ofN m = ofN n ↔ m = n := ⟨ofN.inj, congrArg _⟩

@[simp, norm_cast]
lemma cast_eq_cast_iff_Nat (m n : ℕ) : (m : Enat) = (n : Enat) ↔ m = n := ofN_inj

@[simp]
lemma ofN_eq_ofNat : ofN a = a :=
rfl

-- set_option trace.Meta.Tactic.simp.rewrite true
theorem succ_add (a b : ℕ∪∞) : succ a + b = succ (a + b) := by
  cases a with
  | top => simp [succ]
  | ofN a => cases b with
    | top => simp [succ]
    | ofN b =>
      simp only [Enat.add, ofN_eq_ofNat]
      rw [succ_ofNat, add_ofNat, add_ofNat, succ_ofNat]
      rw [Nat.cast_add, Nat.cast_succ]
      norm_cast
      exact Nat.succ_add a b

theorem add_succ (a b : ℕ∪∞) : a + succ b = succ (a + b) := by
  rw [add_comm, succ_add b a, add_comm]

theorem ofN_mul_eq_smul (a b : ℕ) : (a * b : Enat) = a • (b : Enat) := by
induction a with
| zero => simp [zero_nsmul]
| succ k ih => simp [Nat.succ_mul, succ_nsmul, ← ih, add_comm]

theorem ofNat_mul_eq_smul (a b : ℕ) : (a * b : Enat) = a • (b : Enat) := by
induction a with
| zero => simp [zero_nsmul]
| succ k ih => simp [Nat.succ_mul, succ_nsmul, ← ih, add_comm]

protected theorem lt_top (n : ℕ) : n < ∞ := And.intro Enat.noConfusion le.below_top

protected theorem le_top (n : ℕ) : n ≤ ∞ := le.below_top

@[simp, norm_cast]
protected theorem le_iff_cast_le_cast {n m : ℕ} : (n : Enat) ≤ m ↔ n ≤ m := ⟨by
  intro h
  cases h
  assumption,
  le.in_nat⟩

theorem succ_pos (n : ℕ∪∞) : 0 < succ n :=
  match n with
  | ofN n =>
    .intro Enat.noConfusion (by rw [succ_ofN n]; exact le.in_nat (Nat.succ_le_succ (Nat.zero_le n)))
  | top => Enat.lt_top 0

protected theorem zero_le (n : ℕ∪∞) : 0 ≤ n := by
  cases n with
  | ofN n => exact le.in_nat (Nat.zero_le n)
  | top => exact le.below_top

protected theorem le_refl (n : ℕ∪∞) : n ≤ n := by
  cases n with
  | ofN n => exact le.in_nat (Nat.le_refl n)
  | top     => exact le.below_top

protected theorem le_trans {n m k : ℕ∪∞} : n ≤ m → m ≤ k → n ≤ k
  | le.in_nat h, le.in_nat h' => le.in_nat (Nat.le_trans h h')
  | _, le.below_top                 => le.below_top

theorem le_succ (n : ℕ∪∞) : n ≤ succ n := by
  cases n with
  | ofN n => exact le.in_nat (Nat.le_succ n)
  | top     => exact le.below_top

theorem le_of_succ_le {n m : ℕ∪∞} (h : succ n ≤ m) : n ≤ m :=
  Enat.le_trans (le_succ n) h

protected theorem le_of_lt {n m : ℕ∪∞} (h : n < m) : n ≤ m := by
  cases m with
  | ofN m =>
    cases n with
    | ofN n => exact le_of_succ_le h.right
    | top =>
      apply False.elim
      apply h.left
      rfl
  | top    => exact le.below_top

protected theorem lt_or_ge (n m : ℕ∪∞) : n < m ∨ n ≥ m := by
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

protected theorem not_le_of_gt {n m : ℕ∪∞} (h : n > m) : ¬ n ≤ m := by
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
  match Enat.lt_or_ge m n with
  | Or.inl h₁ => h₁
  | Or.inr h₁ => absurd h₁ h

protected lemma lt_iff_le_not_le {m n : ℕ∪∞} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
⟨fun h => ⟨Enat.le_of_lt h, Enat.not_le_of_gt h⟩, fun h => gt_of_not_le h.2⟩

instance : Preorder ℕ∪∞ :=
{ le               := Enat.le,
  le_refl          := Enat.le_refl,
  le_trans         := @Enat.le_trans,
  lt_iff_le_not_le := @Enat.lt_iff_le_not_le,
  lt               := Enat.lt}

theorem le_add_right (n k : ℕ∪∞) : n ≤ n + k := by cases n with
  | top   => rw [top_add]
  | ofN n => cases k with
    | top   => rw [add_top]; exact le.below_top
    | ofN k => exact le.in_nat (Nat.le_add_right n k)

@[simp]
theorem succ_eq_add_one (a : Enat) : succ a = a + 1 :=
by
  cases a
  . simp
  . simp

theorem le_add_left (n k : ℕ∪∞) : n ≤ k + n := by
  rw [add_comm]
  exact le_add_right n k

protected
theorem add_le_add_left {n m : ℕ∪∞} (h : n ≤ m) (k : ℕ∪∞) : k + n ≤ k + m := by
  cases k with
  | top =>
    simp
  | ofN k => cases n with
    | top => exact le_trans h (le_add_left m (ofN k))
    | ofN n => cases m with
      | top =>
        simp
        exact le.below_top
      | ofN m =>
        simp
        apply le.in_nat
        cases h with
          | in_nat h => exact Nat.add_le_add_left h k

theorem eq_top_of_top_le (a : ℕ∪∞) (h : ∞ ≤ a) : a = ∞ := by
  cases h with
  | below_top => rfl

@[simp]
theorem top_le_iff_eq_top (a : ℕ∪∞) : ∞ ≤ a ↔ a = ∞ :=
Iff.intro (eq_top_of_top_le _) (fun h => by simp [h])

theorem eq_top_of_add_eq_top (a : ℕ∪∞) (n : ℕ) (h : a + n = ∞) : a = ∞ := by
  cases a with
  | top => rfl
  | ofN a => exact Enat.noConfusion h

protected theorem le_of_add_le_add_left {a : ℕ} {b c : ℕ∪∞} (h : a + b ≤ a + c) : b ≤ c :=
by
  cases b with
  | top =>
    simp only [add_comm, top_add, top_le_iff_eq_top] at h
    rw [eq_top_of_add_eq_top c a h]
  | ofN b => cases c with
    | top => exact le.below_top
    | ofN c =>
      apply le.in_nat
      apply @Nat.le_of_add_le_add_left a b
      cases h with
      | in_nat h' => exact h'

theorem succ_le_of_lt {n m : ℕ∪∞} (h : n < m) : succ n ≤ m := h.2

protected theorem le_antisymm {n m : ℕ∪∞} (h1 : n ≤ m) (h2 : m ≤ n) : n = m := by
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

protected theorem le_total (m n : ℕ∪∞) : m ≤ n ∨ n ≤ m :=
  match Enat.lt_or_ge m n with
  | Or.inl h => Or.inl (le_of_lt h)
  | Or.inr h => Or.inr h

@[simp]
lemma le_ofN (m n : Nat) : (m : Enat) ≤ n ↔ m ≤ n := by
  apply Iff.intro
  . intro h
    cases h
    assumption
  .  exact le.in_nat

@[simp]
theorem lt_ofN (m n : ℕ) : (m : Enat) < n ↔ m < n := by
  apply Iff.intro
  . intro h
    cases h.right
    assumption
  . intro h
    exact And.intro (Enat.noConfusion) (le.in_nat h)

lemma eq_ofN (m n : Nat) : m = n ↔ (m : Enat) = n := by
  apply Iff.intro
  . exact congrArg ofN
  . intro h
    cases h
    rfl

instance : DecidableRel ((. ≤ . ) : ℕ∪∞ → ℕ∪∞ → Prop) := fun n m =>
match n, m with
  | ofN b, ofN c =>
  decidable_of_decidable_of_iff (le_ofN b c).symm
  | _, ∞         => isTrue le.below_top
  | ∞, ofN a     => isFalse (fun h => by cases h)

-- instance : DecidableRel ((. = . ) : ℕ∪∞ → ℕ∪∞ → Prop) := fun n m =>
-- match n, m with
--   | ofN b, ofN c =>
--   decidable_of_decidable_of_iff (eq_ofN b c)
--   | ∞, ∞         => isTrue rfl
--   | ∞, ofN a     => isFalse (fun h => by cases h)
--   | ofN a, ∞     => isFalse (fun h => by cases h)

protected theorem eq_zero_or_pos : ∀ (n : ℕ∪∞), n = 0 ∨ n > 0
  | ofN 0   => Or.inl rfl
  | ofN (Nat.succ n) => by rw [←succ_ofN n]; exact Or.inr (succ_pos _)
  | ∞ => Or.inr (Enat.lt_top 0)

protected lemma pos_of_ne_zero {n : ℕ∪∞} : n ≠ 0 → 0 < n :=
Or.resolve_left (Enat.eq_zero_or_pos n)

protected theorem pos_iff_ne_zero (n : ℕ∪∞) : 0 < n ↔ n ≠ 0 :=
Iff.intro ne_of_gt Enat.pos_of_ne_zero

-- TODO  what is the right typeclass that does this?
protected lemma lt_add_right (a b c : ℕ∪∞) : a < b -> a < b + c :=
  fun h => lt_of_lt_of_le h (le_add_right _ _)

-- TODO if min max are left as underscores this becomes noncomputable, another code generator bug?
instance : LinearOrder ℕ∪∞ :=
{ Enat.instPreorderEnat with
  min := fun a b => if a ≤ b then a else b,
  max := fun a b => if a ≤ b then b else a,
  le_antisymm      := @Enat.le_antisymm,
  le_total         := @Enat.le_total,
  decidable_lt     := inferInstance, -- TODO check if these are actually better than the defaults
  decidable_le     := inferInstance,
  decidable_eq     := inferInstance }


@[simp, norm_cast]
protected theorem lt_iff_cast_lt_cast {n m : ℕ} : (n : Enat) < m ↔ n < m :=
by simp [lt_iff_le_and_ne]

theorem add_right_cancel_ofN (a : ℕ) (b c : ℕ∪∞) : b + a = c + a → b = c := by
  cases b with
  | top   => cases c with
    | top   => intro; rfl
    | ofN c =>
      rw [top_add]
      exact fun h => absurd h Enat.noConfusion
  | ofN b => cases c with
    | top   => exact fun h => absurd h Enat.noConfusion
    | ofN c =>
      simp only [ofN_eq_ofNat, cast_eq_cast_iff_Nat]
      norm_cast
      exact Nat.add_right_cancel

theorem add_left_inj_ofN (a : ℕ) {b c : ℕ∪∞} : b + a = c + a ↔ b = c :=
⟨add_right_cancel_ofN a b c, λ h => h ▸ rfl⟩

theorem lt_of_succ_le {n : ℕ} {m : ℕ∪∞} (h : succ n ≤ m) : n < m :=
And.intro Enat.noConfusion h

theorem lt_iff_succ_le {n : ℕ} {m : ℕ∪∞} : n < m ↔ succ n ≤ m :=
Iff.intro succ_le_of_lt lt_of_succ_le

-- TODO this should be automatically derivable
theorem enat_disjunction (a : ℕ∪∞) : a = ∞ ∨ ∃ n : ℕ, a = n :=
  match a with
  | top => Or.inl rfl
  | ofN n => Or.inr (Exists.intro n rfl)

def to_nat {a : ℕ∪∞} (h : a ≠ ∞) : ℕ := by
  cases a with
  | top => exact False.elim (h (Eq.refl ∞))
  | ofN n => exact n

@[simp]
lemma to_nat_ofN {a : ℕ} (h : (a : ℕ∪∞) ≠ ∞) : to_nat h = a := rfl

@[simp]
lemma ofN_to_nat_eq_self {a : ℕ∪∞} (h : a ≠ ∞) : to_nat h = a := by
  cases a with
  | top => exact False.elim (h (Eq.refl ∞))
  | ofN n => rfl

instance : CanonicallyOrderedAddMonoid ℕ∪∞ :=
{ Enat.instLinearOrderEnat with
  bot := 0
  bot_le := Enat.zero_le
  le_self_add := Enat.le_add_right
  exists_add_of_le := by
    intro a b h
    cases b
    case ofN b =>
      cases a
      case ofN a =>
        simp at h
        obtain ⟨c, hc⟩ := exists_add_of_le h
        use c
        simp
        exact_mod_cast hc
      case top =>
        simp at h
    case top =>
      use ∞
      simp
  add_le_add_left := fun _ _ h c => Enat.add_le_add_left h c }

protected def mul : ℕ∪∞ → ℕ∪∞ → ℕ∪∞
  | ofN a, ofN b => ofN (a * b)
  | 0, ∞ => 0
  | ∞, 0 => 0
  | _, ∞ => ∞
  | ∞, _ => ∞

instance : Mul ℕ∪∞ where
  mul := Enat.mul

@[simp]
protected lemma top_mul_top : ∞ * ∞ = ∞ := rfl
protected lemma top_mul_zero : ∞ * 0 = 0 := rfl
protected lemma zero_mul : 0 * (a : ℕ∪∞) = 0 := by
  cases a with | top => rfl | ofN a =>
    show ofN 0 * ofN a = ofN 0
    conv =>
      rhs
      rw [← zero_mul a]


protected lemma mul_coe (a b : ℕ) : (a : Enat) * (b : Enat) = ↑(a * b) :=
by cases a <;> cases b <;> rfl

protected theorem mul_comm (a b : ℕ∪∞) : a * b = b * a := by
  cases a with
  | top =>
  cases b with
    | top => simp
    | ofN b =>
      cases b
      rfl
      rfl
  | ofN a =>
  cases b with
    | top =>
      cases a
      rfl
      rfl
    | ofN b =>
      cases b <;> cases a <;>
      . show ofN (_ * _) = ofN (_ * _)
        rw [Nat.mul_comm]

protected lemma left_distrib (a b c : ℕ∪∞) : a * (b + c) = a * b + a * c :=
match a, b, c with
| ofN a, ofN b, ofN c => by
  simp only [ofN_eq_ofNat, Enat.mul_coe]
  norm_cast
  rw [Enat.mul_coe, left_distrib]
| ∞, ∞, ∞ => rfl
| ∞, ∞, ofN _ => by simp [Enat.mul]
| ∞, ofN _, ∞ => by simp
| ∞, ofN _, ofN 0 => by simp [Enat.top_mul_zero]
| ∞, ofN 0, ofN _ => by simp [Enat.top_mul_zero]
| ∞, ofN (_ + 1), (ofN (_ + 1)) => rfl
| (ofN 0), ∞, ∞ => by simp
| (ofN (_ + 1)), ∞, ∞ => rfl
| (ofN 0), ∞, (ofN 0) => by simp
| (ofN (_ + 1)), ∞, (ofN (_ + 1)) => rfl
| (ofN (0)), ∞, (ofN (_ + 1)) => by simp [Enat.zero_mul]
| (ofN (_ + 1)), ∞, (ofN _) => rfl
| (ofN 0), (ofN _), ∞ => by simp [Enat.zero_mul]
| (ofN (_ + 1)), (ofN _), ∞ => rfl


instance : CommSemiring ℕ∪∞ :=
{ Enat.instAddMonoidWithOneEnat with
  mul := Enat.mul
  add_comm := fun a b => AddCommSemigroup.add_comm a b

  zero_mul := fun a => by cases a with | top => rfl | ofN a =>
      show ofN 0 * ofN a = ofN 0
      conv =>
        rhs
        rw [← zero_mul a]

  mul_comm := fun a b => Enat.mul_comm a b

  mul_zero := fun a => by
      rw [Enat.mul_comm] -- TODO refer to other fields
      cases a with | top => rfl | ofN a =>
      show ofN 0 * ofN a = ofN 0
      conv =>
        rhs
        rw [← zero_mul a]

  one_mul := fun a => by cases a with
    | top => rfl
    | ofN a =>
      show ofN 1 * ofN a = ofN a
      conv =>
        rhs
        rw [← one_mul a]

  mul_one := fun a => by
    rw [Enat.mul_comm] -- TODO refer to other fields
    cases a with
    | top => rfl
    | ofN a =>
      show ofN 1 * ofN a = ofN a
      conv =>
        rhs
        rw [← one_mul a]

  left_distrib := Enat.left_distrib
  right_distrib := fun a b c =>
    by rw [Enat.mul_comm, Enat.left_distrib, Enat.mul_comm b, Enat.mul_comm c]
  mul_assoc := fun a b c => -- TODO this should be automatable
    match a, b, c with
    | ofN a, ofN b, ofN c => by
      simp only [ofN_eq_ofNat, Enat.mul_coe]
      rw [mul_assoc]
    | ∞, ∞, ∞ => rfl
    | ∞, ∞, ofN 0 => rfl
    | ∞, ∞, ofN (_ + 1) => rfl
    | ∞, (ofN 0), ∞ => rfl
    | ∞, (ofN (_ + 1)), ∞ => rfl
    | ∞, (ofN 0), (ofN 0) => rfl
    | ∞, (ofN (_ + 1)), (ofN 0) => rfl
    | ∞, (ofN 0), (ofN (_)) => by simp [Enat.top_mul_zero, Enat.zero_mul]
    | ∞, (ofN (_ + 1)), (ofN (_ + 1)) => rfl
    | (ofN 0), ∞, ∞ => rfl
    | (ofN (_ + 1)), ∞, ∞ => rfl
    | (ofN 0), ∞, (ofN 0) => rfl
    | (ofN (_ + 1)), ∞, (ofN (_ + 1)) => rfl
    | (ofN (0)), ∞, (ofN (_ + 1)) => by simp [Enat.zero_mul]
    | (ofN (_ + 1)), ∞, (ofN 0) => rfl
    | (ofN 0), (ofN _), ∞ => by simp [Enat.zero_mul]
    | (ofN (_ + 1)), (ofN 0), ∞ => rfl
    | (ofN (_ + 1)), (ofN (_ + 1)), ∞ => rfl }

instance : CanonicallyOrderedCommSemiring ℕ∪∞ :=
{ Enat.instCommSemiringEnat, Enat.instCanonicallyOrderedAddMonoidEnat with
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intros a b h
    cases a with
    | top =>
    cases b with
      | top => simp at *
      | ofN b =>
        cases b
        simp at *
        simp [mul_add] at *
    | ofN a =>
    cases b with
      | top =>
        cases a
        simp [add_mul] at *
        simp [add_mul] at *
      | ofN b =>
        cases b <;> cases a <;>
        . simp [mul_add, add_mul] at * <;>
          aesop }
end Enat

-- TODO linter complains about autogenerated decls
-- #lint
