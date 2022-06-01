import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Order
import Mathlib.Algebra.Ring.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Lemmas
import Mathlib.Data.Nat.Enat
import Mathlib.Init.Data.Int.Basic
import Mathlib.Algebra.EllipticCurve.Kronecker

import Mathlib.Tactic.PrintPrefix
--class ValueMonoid (A : Type u) extends AddCommMonoid A, LinearOrder A

section Obvious

lemma lt_mod_eq_self (n : ℕ) {m : ℕ} (h : m < n) : m % n = m := by sorry

end Obvious


open Enat

structure SurjVal {R : Type u} (p : R) [IntegralDomain R] where
  v : R → ℕ∪∞
  v_uniformizer : v p = ofN 1
  v_mul_eq_add_v (a b : R) : v (a * b) = v a + v b
  v_add_ge_min_v (a b : R) : v (a + b) ≥ min (v a) (v b)
  v_eq_top_iff_zero (a : R) : v a = ∞ ↔ a = 0

variable {R : Type u} [IntegralDomain R]

section SurjVal

lemma val_mul_ge_left {p : R} (nav : SurjVal p) (a b : R) : nav.v (a * b) ≥ nav.v a := Enat.le_trans (le_add_right (nav.v a) (nav.v b)) (le_of_eq (nav.v_mul_eq_add_v a b).symm)

lemma val_mul_ge_right {p : R} (nav : SurjVal p) (a b : R) : nav.v (a * b) ≥ nav.v b := by
  rw [mul_comm]
  exact val_mul_ge_left nav b a

lemma val_mul_ge_of_left_ge {p : R} (nav : SurjVal p) {a b : R} (ha : nav.v a ≥ n) : nav.v (a * b) ≥ n := Enat.le_trans ha (val_mul_ge_left nav a b)

lemma val_mul_ge_of_right_ge {p : R} (nav : SurjVal p) {a b : R} (hb : nav.v b ≥ n) : nav.v (a * b) ≥ n := Enat.le_trans hb (val_mul_ge_right nav a b)

lemma val_mul_ge_of_both_ge {p : R} (nav : SurjVal p) {a b : R} (ha : nav.v a ≥ m) (hb : nav.v b ≥ n) : nav.v (a * b) ≥ m + n := by
  rw [nav.v_mul_eq_add_v]
  apply add_le_add ha hb

lemma val_add_ge_of_ge {p : R} (nav : SurjVal p) {a b : R} (ha : nav.v a ≥ n) (hb : nav.v b ≥ n) : nav.v (a + b) ≥ n := Enat.le_trans (le_min ha hb) (nav.v_add_ge_min_v a b)

theorem v_add_eq_min_v {p : R} (nav : SurjVal p) {a b : R} (h : nav.v a < nav.v b) : nav.v (a + b) = nav.v a := sorry --possibly a result?

def nat_of_val {p : R} (nav : SurjVal p) {a : R} (h : a ≠ 0) : ℕ :=
  match nav.v a with
  | ∞ =>
    by apply False.elim; apply h; rw [←nav.v_eq_top_iff_zero a]; sorry
  | ofN n => n

lemma val_of_one {p : R} (nav : SurjVal p) : nav.v 1 = ofN 0 := by
  apply Enat.add_right_cancel_ofN 1
  rw [add_ofN, ←SurjVal.v_uniformizer nav, ←SurjVal.v_mul_eq_add_v nav, one_mul]

lemma val_of_minus_one {p : R} (nav : SurjVal p) : nav.v (-1) = ofN 0 := by sorry

lemma val_of_neg {p : R} (nav : SurjVal p) : nav.v (-x) = nav.v x := by
  rw [←one_mul x, neg_mul_left, nav.v_mul_eq_add_v, val_of_minus_one, one_mul, Enat.zero_add]

theorem val_of_pow_uniformizer {p : R} (nav : SurjVal p) : nav.v (p ^ n) = ofN n := by
  induction n with
  | zero      =>
    rw [pow_zero]
    exact val_of_one nav
  | succ n ih =>
    rw [pow_succ, SurjVal.v_mul_eq_add_v nav, ih, SurjVal.v_uniformizer nav, add_ofN]

end SurjVal

class EnatValRing {R : Type u} (p : R) extends IntegralDomain R where
  valtn : SurjVal p
  decr_val : R → R
  zero_valtn_decr {x : R} (h : valtn.v x = 0) : decr_val x = x
  pos_valtn_decr {x : R} (h : valtn.v x > 0) : x = p * decr_val x
  residue_char : ℕ
  def_char : ∀ n : ℕ, valtn.v (n : R) > 0 ↔ residue_char ∣ n
  norm_repr : R → R --generalization of modulo
  quad_roots_in_residue_field : R → R → R → Bool

def sub_val {R : Type u} {p : R} (evr : EnatValRing p) (x : R) (n : ℕ) : R :=
  match n, evr.valtn.v x with
  | 0, _ => x
  | _, 0 => x
  | Nat.succ n, _ => sub_val evr (evr.decr_val p x) n

lemma sub_val_x_zero {R : Type u} {p : R} (evr : EnatValRing p) (x : R) : sub_val evr x 0 = x := by sorry
--#print prefix sub_val

lemma val_sub_val {R : Type u} {p : R} (evr : EnatValRing p) (x : R) (n : ℕ) (h : evr.valtn.v x = ofN m) : evr.valtn.v (sub_val evr x n) = ofN (m - n) := sorry

lemma factor_p_of_le_val {R : Type u} {p : R} (evr : EnatValRing p) {x : R} {n : ℕ} (h : evr.valtn.v x ≥ ofN n) : x = p ^ n * sub_val evr x n := by sorry

lemma factor_p_of_eq_val {R : Type u} {p : R} (evr : EnatValRing p) {x : R} {n : ℕ} (h : evr.valtn.v x = ofN n) : x = p ^ n * sub_val evr x n := factor_p_of_le_val evr (le_of_eq (Eq.symm h))

lemma sub_val_p_mul {R : Type u} {p : R} (evr : EnatValRing p) (x : R) (n : ℕ) : sub_val evr (p ^ n * x) n = x := by
  induction n with
  | zero      =>
    rw [pow_zero, one_mul]
    exact sub_val_x_zero evr x
  | succ n ih => cases eq_zero_or_pos (evr.valtn.v (p ^ Nat.succ n * x)) with
    | inl => sorry
    | inr => sorry


def has_double_root {R : Type u} {p : R} (evr : EnatValRing p) (a b c : R) :=
  evr.valtn.v a = 0 ∧ evr.valtn.v (b ^ 2 - 4 * a * c) > 0




def nat_prime (p : ℕ) : Prop := 1 < p ∧ (∀ a b : ℕ, (a * b) % p = 0 → a % p = 0 ∨ b % p = 0)

lemma nat_prime_test (p : ℕ) : nat_prime p ↔ (1 < p ∧ (∀ a b : ℕ, a < p → b < p → (a * b) % p = 0 → a % p = 0 ∨ b % p = 0)) := by
  apply Iff.intro
  . intro H
    apply And.intro (H.left)
    intro a b ha hb
    apply H.right a b
  . intro H
    apply And.intro (H.left)
    intro a b p_div_ab
    rw [Nat.mul_mod] at p_div_ab
    have p_pos : p > 0 := lt_trans Nat.zero_lt_one H.left;
    have h := H.right (a % p) (b % p) (Nat.mod_lt a p_pos) (Nat.mod_lt b p_pos) p_div_ab;
    rw [Nat.mod_mod _ p, Nat.mod_mod _ p] at h
    assumption

instance : DecidablePred (nat_prime . : ℕ → Prop) := fun p =>
match p with
  | 0 => sorry --isFalse (not_and_of_not_left _ (not_lt_of_ge (le_of_lt Nat.zero_lt_one)))
  | 1 => isFalse (not_and_of_not_left _ (not_lt_of_ge (le_of_eq rfl)))
  | Nat.succ (Nat.succ p') => sorry



def fmul_eq_addf {R R' : Type u} [Mul R] [Add R'] (f : R → R') (x y : R) : Prop := f (x * y) = f x + f y



namespace Int

lemma natAbs_mul (a b : ℤ) : natAbs (a * b) = natAbs a * natAbs b := by sorry

def nat_valuation : ℕ → ℕ → ℕ∪∞
  | p, 0 => ∞
  | 0, (m+1) => ofN 0
  | 1, (m+1) => ∞
  | (q+2), (m+1) => if (m+1) % (q+2) ≠ 0 then ofN 0 else succ (nat_valuation (q+2) ((m+1) / (q+2)))
termination_by nat_valuation p k =>
  k
decreasing_by
  simp [WellFoundedRelation.rel, measure, invImage, InvImage, Nat.lt_wfRel]
  apply Nat.div_lt_self
  . exact Nat.zero_lt_succ m
  . exact Nat.succ_lt_succ (Nat.zero_lt_succ q)

lemma nat_val_zero (p : ℕ) : nat_valuation p 0 = ∞ := by sorry
lemma nat_val_succ (q m : ℕ) : nat_valuation (q+2) (m+1) = if (m+1) % (q+2) ≠ 0 then ofN 0 else succ (nat_valuation (q+2) ((m+1) / (q+2))) := by rfl


def int_val (p : ℕ) (k : ℤ) : ℕ∪∞ :=
  nat_valuation p (natAbs k)

lemma int_val_uniformizer {p : ℕ} (gt1 : 1 < p) : int_val p p = ofN 1 := by
  delta int_val
  simp
  match p with
  | 0 =>
    apply False.elim
    apply Nat.not_lt_zero 1
    assumption
  | Nat.succ 0 =>
    apply False.elim
    apply Nat.lt_irrefl 1
    assumption
  | q+2 =>
    rw [nat_val_succ, Nat.mod_self, if_neg _]
    rw [Nat.div_self, nat_val_succ, if_pos, succ_ofN]
    rw [lt_mod_eq_self]
    exact Nat.succ_ne_zero 0
    assumption
    exact lt_trans (Nat.lt_succ_self 0) gt1
    exact Ne.irrefl

lemma int_val_mul_eq_add (p : ℕ) (prime : nat_prime p) (a b : ℤ) : fmul_eq_addf (int_val p) a b := by sorry


lemma int_val_add_ge_min (p : ℕ) (a b : ℤ) : int_val p (a + b) ≥ min (int_val p a) (int_val p b) := by sorry

lemma int_val_add_eq_min (p : ℕ) (a b : ℤ) (h : int_val p a < int_val p b) : int_val p (a + b) = (int_val p a) := by sorry

lemma int_val_eq_top_iff_zero (p : ℕ) (gt1 : 1 < p) (a : ℤ) : int_val p a = ∞ ↔ a = 0 := by sorry

def primeVal {p : ℕ} (hp : nat_prime p) : SurjVal (ofNat p) := {
  v := int_val p,
  v_uniformizer := int_val_uniformizer hp.left,
  v_mul_eq_add_v := int_val_mul_eq_add p hp,
  v_add_ge_min_v := int_val_add_ge_min p,
  v_eq_top_iff_zero := int_val_eq_top_iff_zero p hp.left
  }

def decr_val_p (p : ℕ) (val : ℤ → ℕ∪∞) (k : ℤ) : ℤ :=
  match val k with
  | 0 => k
  | _ => k / p

lemma zero_valtn_decr_p {p: ℕ} {k : ℤ} (val : ℤ → ℕ∪∞) (h : val k = 0) : decr_val_p p val k = k := by sorry

def norm_repr_p (p : ℕ) (x : ℤ) : ℤ := (x % (p : ℤ) + p) % (p : ℤ)

def def_char_p (p : ℕ) : ∀ n : ℕ, (primeVal hp).v n > 0 ↔ p ∣ n := sorry

def primeEVR {p : ℕ} (hp : nat_prime p) : EnatValRing (p : ℤ) := {
  valtn := primeVal hp,
  decr_val := decr_val_p p (primeVal hp).v,
  zero_valtn_decr := zero_valtn_decr_p (primeVal hp).v,
  pos_valtn_decr := sorry,
  residue_char := p,
  def_char := def_char_p p,
  norm_repr := norm_repr_p p,
  quad_roots_in_residue_field := fun a b c => Int.quad_root_in_ZpZ a b c p
}

lemma prime_2 : nat_prime 2 := by
  simp only [nat_prime, true_and]
  sorry
lemma prime_3 : nat_prime 3 := by
  simp only [nat_prime, true_and]
  sorry

def modulo (x : ℤ) (p : ℕ) := (x % (p:ℤ) + p) % (p:ℤ)

def inv_mod (x : ℤ) (p : ℕ) := modulo (x ^ (p - 2)) p

def has_double_root (a b c : ℤ) {p : ℕ} (hp : nat_prime p) :=
  let v_p := (primeEVR hp).valtn.v;
  v_p a = 0 ∧ v_p (b ^ 2 - 4 * a * c) > 0

def double_root (a b c : ℤ) (p : ℕ) :=
  if p = 2 then
    modulo c 2
  else
    modulo (-b * inv_mod (2 * a) p) p

lemma val_poly_of_double_root {p : ℕ} (hp : nat_prime p) (a b c : ℤ) (H : has_double_root a b c hp) : let x := double_root a b c p; let v_p := (primeEVR hp).valtn.v; v_p (a*x^2 + b*x + c) > 0 ∧ v_p (2*a*x + b) > 0 := by sorry



end Int
