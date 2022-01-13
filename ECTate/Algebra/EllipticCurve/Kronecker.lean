import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Logic.Basic
import Mathlib.Init.Algebra.Order


open Nat

section Obvious

lemma even_or_odd (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by sorry
lemma le_zero {n : ℕ} (h : n ≤ 0) : n = 0 := by sorry
  -- not_succ_le_zero
lemma div_succ_le_succ_div (m n : ℕ) : succ m / succ n ≤ succ (m / succ n) := by sorry
lemma div2_succ_succ_eq_succ_div2 (n : ℕ) : succ (succ n) / 2 = succ (n / 2) := by sorry

end Obvious

namespace Int

lemma div2_lt_self {x : ℕ} (h : 0 < x) : x / 2 < x :=
  div_lt_self h (lt_succ_self 1)
lemma div2_succ_le_self (x : ℕ) : succ x / 2 ≤ x := by
  cases x with
  | zero => simp
  | succ x =>
    have ssxd2_le_s_sxd2 := div_succ_le_succ_div (succ x) 1;
    have s_sxd2_le_sx := succ_le_of_lt (div2_lt_self (succ_pos x));
    exact le_trans ssxd2_le_s_sxd2 s_sxd2_le_sx



def val_bin_nat (x : ℕ) : ℕ × ℕ :=
  if h : 0 < x ∧ x % 2 = 0 then
    let vbn_half := val_bin_nat (x / 2);
    (vbn_half.fst + 1, vbn_half.snd)
  else if 0 < x then
    (0, x)
  else
    (0, 0)
termination_by
  measure id
decreasing_by
  simp [measure, invImage, InvImage, lt_wfRel]
  exact div2_lt_self h.left

def val_bin (x : ℤ) : ℕ × ℤ :=
  let (v, r) := val_bin_nat (natAbs x);
  (v, sign x * r)

lemma odd_part_le_self_nat (x : ℕ) : (val_bin_nat x).2 ≤ x := by
  have acc : ∀ y, y ≤ x → (val_bin_nat y).2 ≤ x := by
    induction x with
    | zero =>
      intro y h
      rw [le_zero h]
      exact zero_le 0
    | succ x ih =>
      intro y y_le_sx
      cases y_le_sx with
      | refl =>
        cases even_or_odd (succ x) with
        | inl even =>
          have h : 0 < succ x ∧ succ x % 2 = 0 :=
          And.intro (zero_lt_succ x) even;
          show (if 0 < succ x ∧ succ x % 2 = 0 then
          let vbn_half := val_bin_nat (succ x / 2);
          (vbn_half.fst + 1, vbn_half.snd)
          else if 0 < succ x then
          (0, succ x)
          else
          (0, 0)).snd ≤ succ x
          rw [if_pos h]
          have h' := ih (succ x / 2) (div2_succ_le_self x);
          --show (val_bin_nat (succ x / 2)).snd ≤ succ x
          exact le_trans h' (le_succ x)
        | inr odd =>
          show (if 0 < succ x ∧ succ x % 2 = 0 then
          let vbn_half := val_bin_nat (succ x / 2);
          (vbn_half.fst + 1, vbn_half.snd)
          else if 0 < succ x then
          (0, succ x)
          else
          (0, 0)).snd ≤ succ x
          have not_even : succ x % 2 ≠ 0 := by
            rw [odd]
            simp;
          rw [if_neg (not_and_of_not_right (0 < succ x) not_even)]
          rw [if_pos (zero_lt_succ x)]
          exact le_refl (succ x)
      | step y_le_x => exact le_trans (ih y y_le_x) (le_succ x);
  exact acc x (le_refl x)

lemma odd_part_succ_pos (x : ℕ) : 0 < (val_bin_nat (succ x)).2 := by
  have acc : ∀ y, (y ≤ x → 0 < (val_bin_nat (succ y)).2) := by
    induction x with
    | zero =>
      intro y y_le_x
      rw [le_zero y_le_x]
      exact lt_succ_self 0
    | succ x ih =>
      intro y y_le_sx
      cases y_le_sx with
      | refl =>
        cases even_or_odd (succ (succ x)) with
        | inl even =>
          have h : 0 < succ (succ x) ∧ succ (succ x) % 2 = 0 :=
          And.intro (zero_lt_succ (succ x)) even;
          show 0 < (if 0 < succ (succ x) ∧ succ (succ x) % 2 = 0 then
          let vbn_half := val_bin_nat (succ (succ x) / 2);
          (vbn_half.fst + 1, vbn_half.snd)
          else if 0 < succ (succ x) then
          (0, succ (succ x))
          else
          (0, 0)).snd
          rw [if_pos h, div2_succ_succ_eq_succ_div2]
          exact ih (x / 2) (Nat.div_le_self x 2)
        | inr odd =>
          show 0 < (if 0 < succ (succ x) ∧ succ (succ x) % 2 = 0 then
          let vbn_half := val_bin_nat (succ (succ x) / 2);
          (vbn_half.fst + 1, vbn_half.snd)
          else if 0 < succ (succ x) then
          (0, succ (succ x))
          else
          (0, 0)).snd
          have not_even : succ (succ x) % 2 ≠ 0 := by
            rw [odd]
            simp;
          rw [if_neg (not_and_of_not_right (0 < succ (succ x)) not_even)]
          rw [if_pos (zero_lt_succ (succ x))]
          exact zero_lt_succ (succ x)
      |step y_le_x => exact ih y y_le_x;
  exact acc x (le_refl x)

lemma odd_part_nat_pos (x : ℕ) : x ≠ 0 → 0 < (val_bin_nat x).2 := by
  cases x with
  | zero =>
    intro absurd
    apply False.elim
    apply absurd
    rfl
  | succ x =>
    intro _
    exact odd_part_succ_pos x

def kronecker_2 (x : ℕ) : ℤ := match x % 8 with
  | 1 => 1 | 7 => 1
  | 3 => -1 | 5 => -1
  | _ => 0

def kronecker_odd (k : ℤ) (a b : ℕ) : ℤ :=
  -- b is odd and a, b ≥ 0
  if h : a = 0 then if b > 1 then 0 else k else
  let v_r := val_bin_nat a;
  let k' := if v_r.fst % 2 = 0 then k else k * (kronecker_2 b);
  let k'' := if v_r.snd % 4 = 3 ∧ b % 4 = 3 then k' else -k';
  kronecker_odd k'' (b % v_r.snd) v_r.snd
termination_by
  measure (fun ⟨k, a, b⟩ => a)
decreasing_by
  simp [measure, invImage, InvImage, lt_wfRel]
  apply lt_of_lt_of_le _ (odd_part_le_self_nat _)
  apply mod_lt
  apply odd_part_nat_pos
  assumption


def kronecker (a b : ℤ) : ℤ :=
  if b = 0 then if natAbs a = 1 then 1 else 0 else
  if b % 2 = 0 ∧ a % 2 = 0 then 0 else
  let (v2b, b') := val_bin b;
  let k := if v2b % 2 = 0 then 1 else kronecker_2 (natAbs a);
  let k' := if b' < 0 ∧ a < 0 then -k else k;
  let abs_b' := natAbs b';
  let a_residue := natAbs (if a < 0 then a % ofNat abs_b' + abs_b' else a % ofNat abs_b');
  kronecker_odd k' a_residue abs_b'

def ex_root_quad (a b c p : ℤ) : Bool :=
  let (a', b', c') := (a % p, b % p, c % p);
  kronecker ((b' * b' - 4 * a' * c') % p) p = 1

end Int
