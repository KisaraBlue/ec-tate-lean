import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Order
import ECTate.Algebra.Ring.Basic
import Mathlib.Init.Data.Nat.Lemmas
import ECTate.Init.Data.Int.Lemmas
import ECTate.Data.Nat.Enat
import ECTate.Algebra.EllipticCurve.Kronecker
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
--class ValueMonoid (A : Type u) extends AddCommMonoid A, LinearOrder A

open Enat

section Obvious

lemma match_non_zero (x : ℕ∪∞) {c1 c2 : β} : x ≠ 0 → (match x with | 0 => c1 | _ => c2) = c2 := by
  intro h
  match x with
  | ofN 0 => exact False.elim (h (Eq.refl 0))
  | ∞ => simp
  | ofN (_ + 1) => simp

theorem nat_mul_left_cancel (a b c : Nat) (h : a ≠ 0) : a * b = a * c → b = c :=
Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h)

end Obvious

structure SurjVal {R : Type u} (p : R) [IntegralDomain R] where
  v : R → ℕ∪∞
  v_uniformizer : v p = 1
  v_mul_eq_add_v (a b : R) : v (a * b) = v a + v b
  v_add_ge_min_v (a b : R) : v (a + b) ≥ min (v a) (v b)
  v_eq_top_iff_zero (a : R) : v a = ∞ ↔ a = 0

variable {R : Type u} [IntegralDomain R]

section SurjVal

lemma p_non_zero {p : R} (nav : SurjVal p) : ¬p = 0 := by
  rw [←nav.v_eq_top_iff_zero, nav.v_uniformizer]
  simp

@[simp]
lemma val_zero {p : R} (nav : SurjVal p) : nav.v 0 = ∞ := (nav.v_eq_top_iff_zero 0).2 rfl

lemma val_mul_ge_left {p : R} (nav : SurjVal p) (a b : R) : nav.v (a * b) ≥ nav.v a :=
le_trans (le_add_right (nav.v a) (nav.v b)) (le_of_eq (nav.v_mul_eq_add_v a b).symm)

lemma val_mul_ge_right {p : R} (nav : SurjVal p) (a b : R) : nav.v (a * b) ≥ nav.v b := by
  rw [mul_comm]
  exact val_mul_ge_left nav b a

lemma val_mul_ge_of_left_ge {p : R} (nav : SurjVal p) {a b : R} (ha : nav.v a ≥ n) :
nav.v (a * b) ≥ n :=
le_trans ha (val_mul_ge_left nav a b)

lemma val_mul_ge_of_right_ge {p : R} (nav : SurjVal p) {a b : R} (hb : nav.v b ≥ n) :
nav.v (a * b) ≥ n :=
le_trans hb (val_mul_ge_right nav a b)

lemma val_mul_ge_of_both_ge {p : R} (nav : SurjVal p) {a b : R} (ha : nav.v a ≥ m) (hb : nav.v b ≥ n) :
nav.v (a * b) ≥ m + n := by
  rw [nav.v_mul_eq_add_v]
  apply add_le_add ha hb

@[simp]
lemma val_of_one {p : R} (nav : SurjVal p) : nav.v 1 = 0 := by
  apply Enat.add_right_cancel_ofN 1
  simp only [Nat.cast_one, zero_add]
  rw [←SurjVal.v_uniformizer nav, ←SurjVal.v_mul_eq_add_v nav, one_mul]

lemma val_pow_ge_of_ge {p : R} (nav : SurjVal p) {a : R} (k : ℕ) (ha : nav.v a ≥ m) :
nav.v (a ^ k) ≥ k • m := by
  induction k with
  | zero => simp [zero_nsmul] -- TODO why isn't this simp?
  | succ k ih =>
    simp only [succ_nsmul, pow_succ]
    apply val_mul_ge_of_both_ge _ ha ih

lemma val_pow_eq_of_eq {p : R} (nav : SurjVal p) {a : R} (k : ℕ) (ha : nav.v a = m) :
nav.v (a ^ k) = k * m := by
  induction k with
  | zero => simp [zero_nsmul] -- TODO why isn't this simp?
  | succ k ih =>
    simp only [pow_succ, Nat.cast_succ, add_mul, one_mul, add_comm]
    rw [nav.v_mul_eq_add_v, ha, ih]

lemma val_add_ge_of_ge {p : R} (nav : SurjVal p) {a b : R} (ha : nav.v a ≥ n) (hb : nav.v b ≥ n) :
nav.v (a + b) ≥ n := le_trans (le_min ha hb) (nav.v_add_ge_min_v a b)

def nat_of_val {p : R} (nav : SurjVal p) {a : R} (h : a ≠ 0) : ℕ :=
  to_nat ((not_iff_not.2 (nav.v_eq_top_iff_zero a)).2 h)

/-
lemma val_of_add_one {p : R} (nav : SurjVal p) (h : nav.v x ≥ 1): nav.v (x + 1) = 0 := by
  apply le_antisymm
  . apply le_of_not_lt
    intro h'
    sorry
  . apply le_trans _ (nav.v_add_ge_min_v x 1)
    apply le_min (le_trans (le_succ 0) h) (le_of_eq (val_of_one nav).symm)
-/

@[simp]
lemma val_of_minus_one {p : R} (nav : SurjVal p) : nav.v (-1) = 0 := by
  cases eq_zero_or_pos (nav.v (-1)) with
  | inl h => exact h
  | inr h =>
    have contradiction : nav.v 1 > 0 := by
      rw [←neg_neg 1, ←one_mul 1, neg_mul_left, neg_mul_right, nav.v_mul_eq_add_v]
      apply lt_add_right _ _ _ h
    rw [val_of_one] at contradiction
    exact False.elim ((lt_irrefl 0) contradiction)

@[simp]
lemma val_neg {p : R} (nav : SurjVal p) : nav.v (-x) = nav.v x := by
  rw [←one_mul x, neg_mul_left, nav.v_mul_eq_add_v, val_of_minus_one, one_mul, zero_add]

lemma val_sub_ge_of_ge {p : R} (nav : SurjVal p) {a b : R} (ha : nav.v a ≥ n) (hb : nav.v b ≥ n) :
nav.v (a - b) ≥ n := by
  rw [sub_eq_add_neg]
  apply val_add_ge_of_ge
  assumption
  simpa

theorem v_add_eq_min_v {p : R} (nav : SurjVal p) {a b : R} (h : nav.v a < nav.v b) :
  nav.v (a + b) = nav.v a := by
  apply le_antisymm
  . apply le_of_not_lt
    intro h'
    have hm : nav.v a < nav.v (-b) := by rwa [val_neg]
    apply lt_irrefl (nav.v a)
    apply lt_of_lt_of_le (lt_min h' hm)
    rw [(show nav.v a = nav.v (a + b + -b) by simp)]
    exact nav.v_add_ge_min_v (a + b) (-b)
  . exact le_trans (le_min (le_of_eq rfl) (le_of_lt h)) (SurjVal.v_add_ge_min_v nav a b)

theorem val_of_pow_uniformizer {p : R} (nav : SurjVal p) {n : ℕ} : nav.v (p ^ n) = n := by
  induction n with
  | zero      =>
    rw [pow_zero]
    exact val_of_one nav
  | succ n ih =>
    rw [pow_succ, SurjVal.v_mul_eq_add_v nav, ih, SurjVal.v_uniformizer nav]
    simp [Nat.succ_eq_add_one, add_comm]

end SurjVal

structure EnatValRing {R : Type u} (p : R) [IntegralDomain R] where
  valtn : SurjVal p
  decr_val : R → R
  zero_valtn_decr {x : R} (h : valtn.v x = 0) : decr_val x = x
  pos_valtn_decr {x : R} (h : valtn.v x > 0) : x = p * decr_val x
  residue_char : ℕ -- ToDo delete
  norm_repr : R → R --generalization of modulo
  quad_roots_in_residue_field : R → R → R → Bool

namespace EnatValRing

/-- reduce the element x by valuation n (by dividing by an appropriate power of the uniformizer) -/
def sub_val {p : R} (evr : EnatValRing p) (x : R) (n : ℕ) : R :=
  match n with
  | 0 => x
  | Nat.succ n =>
    match evr.valtn.v x with
    | 0 => x
    | _ => sub_val evr (evr.decr_val x) n

@[simp]
lemma decr_val_zero {p : R} (evr : EnatValRing p) : evr.decr_val 0 = 0 := by
  have v_decr_zero : p * evr.decr_val 0 = 0 := by
    apply Eq.symm
    apply evr.pos_valtn_decr
    rw [val_zero]
    exact Enat.lt_top 0
  rw [mul_eq_zero_iff_factor_eq_zero] at v_decr_zero
  exact Or.resolve_left v_decr_zero (p_non_zero evr.valtn)

@[simp]
lemma decr_val_neg {p : R} (evr : EnatValRing p) (x : R) : evr.decr_val (-x) = -evr.decr_val x := by
  cases eq_zero_or_pos (evr.valtn.v x) with
  | inl h =>
    have hm : evr.valtn.v (-x) = 0 := by simp [h]
    rw [evr.zero_valtn_decr h, evr.zero_valtn_decr hm]
  | inr h =>
    have hm : evr.valtn.v (-x) > 0 := by simp [h]
    apply nzero_mul_left_cancel p _ _ (p_non_zero evr.valtn)
    rw [←neg_mul_right, ←evr.pos_valtn_decr h, ←evr.pos_valtn_decr hm]

@[simp]
lemma decr_val_p_mul {p : R} (evr : EnatValRing p) (x : R) : evr.decr_val (p * x) = x := by
  have h : (p * x) = p * decr_val evr (p * x) := by
    apply evr.pos_valtn_decr
    rw [evr.valtn.v_mul_eq_add_v, evr.valtn.v_uniformizer]
    apply lt_of_lt_of_le ((Enat.lt_ofN 0 1).1 (Nat.lt_succ_self 0)) (le_add_right 1 _)
  apply nzero_mul_left_cancel p _ _ (p_non_zero evr.valtn)
  exact h.symm

@[simp]
lemma sub_val_zero_n {p : R} (evr : EnatValRing p) (n : ℕ) : sub_val evr 0 n = 0 := by
  induction n with
  | zero => simp [sub_val]
  | succ n ih => simpa [sub_val, decr_val_zero]

@[simp]
lemma sub_val_x_zero {p : R} (evr : EnatValRing p) (x : R) : sub_val evr x 0 = x := by rfl

lemma sub_val_val_zero {p : R} (evr : EnatValRing p) (x : R) (m : ℕ) (h : evr.valtn.v x = 0) :
  sub_val evr x m = x := by
  cases m with
  | zero => exact sub_val_x_zero evr x
  | succ m => simp [sub_val, h]

lemma sub_val_val_pos_succ {p : R} (evr : EnatValRing p) (x : R) (m : ℕ) (h : evr.valtn.v x ≠ 0) :
  sub_val evr x (Nat.succ m) = sub_val evr (evr.decr_val x) m := by
  simp [sub_val, h]

lemma val_decr_val {p : R} (evr : EnatValRing p) {m : Nat} (x : R) (h : evr.valtn.v x = m) :
  evr.valtn.v (evr.decr_val x) = ↑(m - 1) := by
  cases m with
  | zero => rwa [evr.zero_valtn_decr h]
  | succ m =>
    have x_pos_val : evr.valtn.v x > 0 := by
      rw [h]
      exact succ_pos m
    apply add_right_cancel_ofN 1
    simp at * -- TODO fix nonterminal
    rw [←evr.valtn.v_uniformizer, ←evr.valtn.v_mul_eq_add_v, mul_comm,
      ←evr.pos_valtn_decr x_pos_val, h, evr.valtn.v_uniformizer]

lemma sub_val_decr_val_comm {p : R} (evr : EnatValRing p) (x : R) (n : ℕ) :
  sub_val evr (evr.decr_val x) n = evr.decr_val (sub_val evr x n) := by
  have general : ∀ a, sub_val evr (evr.decr_val a) n = evr.decr_val (sub_val evr a n) := by
    induction n with
    | zero =>
      simp [sub_val_x_zero]
    | succ n ih =>
      intro a
      cases Enat.eq_zero_or_pos (evr.valtn.v a) with
      | inl h =>
        rw [evr.zero_valtn_decr h, sub_val_val_zero evr a n.succ h, evr.zero_valtn_decr h]
      | inr h =>
        cases Enat.eq_zero_or_pos (evr.valtn.v (evr.decr_val a)) with
        | inl h' =>
          rw [sub_val_val_zero evr (evr.decr_val a) n.succ h', sub_val_val_pos_succ evr a n (ne_of_gt h), ←ih (evr.decr_val a), evr.zero_valtn_decr h', sub_val_val_zero evr (evr.decr_val a) n h']
        | inr h' =>
          rw [sub_val_val_pos_succ evr (evr.decr_val a) n (ne_of_gt h'), ih (evr.decr_val a), sub_val_val_pos_succ evr a n (ne_of_gt h)]
  exact general x

lemma val_sub_val_eq {p : R} (evr : EnatValRing p) (x : R) {m : ℕ} (n : ℕ) (h : evr.valtn.v x = m) :
  evr.valtn.v (sub_val evr x n) = ↑(m - n) := by
  induction n with
  | zero => rwa [sub_val_x_zero, Nat.sub_zero]
  | succ n ih =>
    cases m with
    | zero =>
      rw [Nat.zero_sub] at ih
      rw [Nat.zero_sub, sub_val_val_zero evr x n.succ h]
      exact h
    | succ m =>
      rw [sub_val_val_pos_succ, sub_val_decr_val_comm, val_decr_val evr (sub_val evr x n) ih,
        Nat.succ_eq_add_one n, Nat.sub_sub]
      rw [h]
      norm_cast at *

lemma val_sub_val_le {p : R} (evr : EnatValRing p) (x : R) {m : ℕ} (n : ℕ) (h : evr.valtn.v x ≥ m) :
  evr.valtn.v (sub_val evr x n) ≥ ↑(m - n) := by
  cases enat_disjunction (evr.valtn.v x) with
  | inl h' =>
    have topcase : x = 0 := (evr.valtn.v_eq_top_iff_zero x).1 h'
    rw [topcase, sub_val_zero_n, (evr.valtn.v_eq_top_iff_zero 0).2 rfl]
    exact le.below_top
  | inr h' =>
    have H : ∀ (a : ℕ), evr.valtn.v x = a → evr.valtn.v (sub_val evr x n) ≥ (m - n) := by
      intro a ha
      have h'' := val_sub_val_eq evr x n ha
      rw [h'']
      apply (le_ofN (m - n) (a - n)).1
      rw [ha] at h
      apply Nat.sub_le_sub_right ((le_ofN m a).2 h)
    exact Exists.elim h' H

lemma factor_p_of_le_val {p : R} (evr : EnatValRing p) {x : R} {n : ℕ} (h : evr.valtn.v x ≥ n) :
  x = p ^ n * sub_val evr x n := by
  induction n with
  | zero => simp [sub_val]
  | succ n ih =>
    rw [sub_val_val_pos_succ, sub_val_decr_val_comm, pow_succ', mul_assoc]
    have pos_val : evr.valtn.v (sub_val evr x n) > 0 := by
      have h' := val_sub_val_le evr x n h
      rw [Nat.succ_eq_add_one, Nat.add_sub_self_left] at h'
      exact lt_of_succ_le h'
    rw [←evr.pos_valtn_decr pos_val]
    apply ih
    exact le_of_succ_le h
    apply ne_of_gt
    rw [Nat.cast_succ] at h
    exact lt_of_lt_of_le (succ_pos n) h

lemma factor_p_of_eq_val {p : R} (evr : EnatValRing p) {x : R} {n : ℕ} (h : evr.valtn.v x = n) :
x = p ^ n * sub_val evr x n := factor_p_of_le_val evr (le_of_eq (Eq.symm h))

lemma sub_val_p_mul {p : R} (evr : EnatValRing p) (x : R) (n : ℕ) : sub_val evr (p ^ n * x) n = x := by
  induction n with
  | zero      =>
    rw [pow_zero, one_mul]
    exact sub_val_x_zero evr x
  | succ n ih =>
    rwa [sub_val_val_pos_succ evr, pow_succ, mul_assoc, decr_val_p_mul]
    apply ne_of_gt
    apply lt_of_succ_le
    simp only [Nat.zero_eq, Nat.cast_zero, succ_zero]
    rw [pow_succ, mul_assoc, ←evr.valtn.v_uniformizer]
    apply val_mul_ge_left evr.valtn

lemma sub_val_neg {p : R} (evr : EnatValRing p) {x : R} {n : ℕ} : sub_val evr (-x) n = -sub_val evr x n := by
  induction n with
  | zero => simp [sub_val_x_zero]
  | succ n ih =>
    cases eq_zero_or_pos (evr.valtn.v x) with
    | inl h' =>
      have h'm : evr.valtn.v (-x) = 0 := by simp [h']
      rw [sub_val_val_zero evr _ _ h', sub_val_val_zero evr _ _ h'm]
    | inr h' =>
      have h'm : evr.valtn.v (-x) > 0 := by simp [h']
      rw [sub_val_val_pos_succ evr _ _ (ne_of_gt h'), sub_val_val_pos_succ evr _ _ (ne_of_gt h'm), sub_val_decr_val_comm, ih, decr_val_neg, sub_val_decr_val_comm]

lemma sub_val_add {p : R} (evr : EnatValRing p) {x y : R} {n : ℕ} (hx : evr.valtn.v x ≥ n)
  (hy : evr.valtn.v y ≥ n) : sub_val evr (x + y) n = sub_val evr x n + sub_val evr y n := by
  apply nzero_mul_left_cancel (p ^ n)
  . exact pow_nonzero p n (p_non_zero evr.valtn)
  . rw [←factor_p_of_le_val evr (_ : evr.valtn.v (x + y) ≥ n), mul_add, ←factor_p_of_le_val evr hx, ←factor_p_of_le_val evr hy]
    exact le_trans (le_min hx hy) (evr.valtn.v_add_ge_min_v x y)

lemma sub_val_sub {p : R} (evr : EnatValRing p) {x y : R} {n : ℕ} (hx : evr.valtn.v x ≥ n)
  (hy : evr.valtn.v y ≥ n) : sub_val evr (x - y) n = sub_val evr x n - sub_val evr y n :=
by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_val_add evr hx, sub_val_neg]
  simpa

lemma sub_val_mul_left {p : R} (evr : EnatValRing p) {x y : R} {n : ℕ} (hx : evr.valtn.v x ≥ n) :
  sub_val evr (x * y) n = sub_val evr x n * y := by
  apply nzero_mul_left_cancel (p ^ n)
  . exact pow_nonzero p n (p_non_zero evr.valtn)
  . rw [←factor_p_of_le_val evr (_ : evr.valtn.v (x * y) ≥ n), ←mul_assoc, ←factor_p_of_le_val evr hx]
    exact le_trans hx (val_mul_ge_left evr.valtn x y)

lemma sub_val_mul_right {p : R} (evr : EnatValRing p) {x y : R} {n : ℕ} (hy : evr.valtn.v y ≥ n) :
  sub_val evr (x * y) n = x * sub_val evr y n :=
by rw [mul_comm x y, sub_val_mul_left evr hy, mul_comm]

lemma sub_val_mul_sub_val {p : R} (evr : EnatValRing p) {x y : R} (n m : ℕ)
  (hx : evr.valtn.v x ≥ n) (hy : evr.valtn.v y ≥ m) :
  sub_val evr x n * sub_val evr y m = sub_val evr (x * y) (n + m) := by
  apply nzero_mul_left_cancel (p ^ (n + m)) _ _ (pow_nonzero p _ (p_non_zero evr.valtn))
  rw [←factor_p_of_le_val evr (_ : evr.valtn.v (x * y) ≥ (n + m)), pow_add, mul_assoc,
    mul_comm (p ^ m), ← mul_assoc,
    ← mul_assoc,
    ←factor_p_of_le_val evr (_ : evr.valtn.v x ≥ n), mul_assoc, mul_comm _ (p ^ m),
    ←factor_p_of_le_val evr (_ : evr.valtn.v y ≥ m)]
  . assumption
  . assumption
  . rw [SurjVal.v_mul_eq_add_v]
    exact add_le_add hx hy

lemma sub_val_mul {p : R} (evr : EnatValRing p) {x y : R} (n m : ℕ) {nm : ℕ} (h : n + m = nm)
  (hx : evr.valtn.v x ≥ n) (hy : evr.valtn.v y ≥ m) :
  sub_val evr (x * y) nm = sub_val evr x n * sub_val evr y m := by
  rw [← h, sub_val_mul_sub_val _ _ _ hx hy]

lemma sub_val_pow {p : R} (evr : EnatValRing p) {x : R} (n k : ℕ) {nm : ℕ} (h : k * n = nm)
  (hx : evr.valtn.v x ≥ n) :
  sub_val evr (x ^ k) nm = sub_val evr x n ^ k := by
  induction k generalizing nm with
  | zero => simp [← h]
  | succ k ih =>
    rw [pow_succ, sub_val_mul _ n (k * n), pow_succ, ← ih]
    rfl
    rw [← h, Nat.succ_mul, add_comm]
    exact hx
    convert val_pow_ge_of_ge evr.valtn k hx
    exact ofNat_mul_eq_smul k n

lemma sub_val_sub_val {p : R} (evr : EnatValRing p) {x : R} {m n : ℕ} :
  sub_val evr (sub_val evr x m) n = sub_val evr x (m + n) := by
  have general : ∀ y : R, sub_val evr (sub_val evr y m) n = sub_val evr y (m + n) := by
    induction m with
    | zero => simp [sub_val_x_zero]
    | succ m ih =>
      intro y
      cases eq_zero_or_pos (evr.valtn.v y) with
      | inl h' => simp [sub_val_val_zero evr y _ h']
      | inr h' =>
        rw [sub_val_val_pos_succ evr y m (ne_of_gt h'), Nat.succ_add, sub_val_val_pos_succ evr y _ (ne_of_gt h')]
        exact ih (evr.decr_val y)
  exact general x

def has_double_root {p : R} (evr : EnatValRing p) (a b c : R) :=
  evr.valtn.v a = 0 ∧ evr.valtn.v (b ^ 2 - 4 * a * c) > 0

end EnatValRing


def nat_prime (p : ℕ) : Prop := 1 < p ∧ (∀ a b : ℕ, (a * b) % p = 0 → a % p = 0 ∨ b % p = 0)

lemma ndiv_mul_left (a b p : ℕ) : (a * b) % p ≠ 0 → a % p ≠ 0 := by
  intro hab ha
  apply hab
  simp [Nat.mul_mod, ha]

lemma ndiv_mul_right (a b p : ℕ) : (a * b) % p ≠ 0 → b % p ≠ 0 := by
  rw [Nat.mul_comm]
  exact ndiv_mul_left b a p

lemma nat_prime_test (p : ℕ) : nat_prime p ↔ (1 < p ∧ (∀ a b : ℕ, a < p → b < p → (a * b) % p = 0 → a % p = 0 ∨ b % p = 0)) := by
  apply Iff.intro
  . intro H
    apply And.intro (H.left)
    intro a b _ _
    apply H.right a b
  . intro H
    apply And.intro (H.left)
    intro a b p_div_ab
    rw [Nat.mul_mod] at p_div_ab
    have p_pos : p > 0 := lt_trans Nat.zero_lt_one H.left;
    have h := H.right (a % p) (b % p) (Nat.mod_lt a p_pos) (Nat.mod_lt b p_pos) p_div_ab;
    rwa [Nat.mod_mod _ p, Nat.mod_mod _ p] at h



instance : DecidablePred (nat_prime . : ℕ → Prop) := fun p => sorry
--match p with
  --| 0 => sorry --isFalse (not_and_of_not_left _ (not_lt_of_ge (le_of_lt Nat.zero_lt_one)))
  --| 1 => isFalse (not_and_of_not_left _ (not_lt_of_ge (le_of_eq rfl)))
  --| Nat.succ (Nat.succ p') => sorry



--def fmul_eq_addf {R R' : Type u} [Mul R] [Add R'] (f : R → R') (x y : R) : Prop := f (x * y) = f x + f y



-- @[extern "blah"]
-- def nat_valuation_aux : ℕ → ℕ → ℕ
--   | _, 0 => 0
--   | 0, (_+1) => 0
--   | 1, (_+1) => 0
--   | (q+2), (m+1) => if (m+1) % (q+2) ≠ 0 then 0 else Nat.succ (nat_valuation_aux (q+2) ((m+1) / (q+2)))
-- termination_by nat_valuation_aux p k => k
-- decreasing_by
--   simp [WellFoundedRelation.rel, measure, invImage, InvImage, Nat.lt_wfRel]
--   exact Nat.div_lt_self (Nat.zero_lt_succ m) (Nat.succ_lt_succ (Nat.zero_lt_succ q))

def nat_valuation : ℕ → ℕ → ℕ∪∞
  | _, 0 => ∞
  | 0, (_+1) => 0
  | 1, (_+1) => ∞
  | (q+2), (m+1) => if (m+1) % (q+2) ≠ 0 then 0 else succ (nat_valuation (q+2) ((m+1) / (q+2)))
termination_by nat_valuation p k => k
decreasing_by
  simp [WellFoundedRelation.rel, measure, invImage, InvImage, Nat.lt_wfRel]
  exact Nat.div_lt_self (Nat.zero_lt_succ m) (Nat.succ_lt_succ (Nat.zero_lt_succ q))

#eval Nat.succ 2147483648
lemma nat_val_zero (p : ℕ) : nat_valuation p 0 = ∞ := by
  simp [nat_valuation]
lemma nat_val_succ (q m : ℕ) : nat_valuation (q+2) (m+1) = if (m+1) % (q+2) ≠ 0 then 0 else succ (nat_valuation (q+2) ((m+1) / (q+2))) := by rfl


namespace Int

def int_val (p : ℕ) (k : ℤ) : ℕ∪∞ :=
  nat_valuation p (natAbs k)

lemma int_val_uniformizer {p : ℕ} (gt1 : 1 < p) : int_val p p = 1 := by
  simp only [natAbs_cast, int_val]
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
    rw [Nat.div_self, nat_val_succ, if_pos, succ_zero]
    rw [Nat.mod_eq_of_lt]
    exact Nat.succ_ne_zero 0
    assumption
    exact lt_trans (Nat.lt_succ_self 0) gt1
    exact Ne.irrefl

lemma nat_val_mul_eq_add (p : ℕ) (prime : nat_prime p) (a b : ℕ) :
  nat_valuation p (a * b) = nat_valuation p a + nat_valuation p b := by
  have general (n : ℕ) : ∀ c d, c + d ≤ n → nat_valuation p (c * d) = nat_valuation p c + nat_valuation p d := by
    induction n with
    | zero =>
      intro c d h_sum
      rw [Nat.eq_zero_of_add_eq_zero_right (Nat.eq_zero_of_le_zero h_sum),
        Nat.eq_zero_of_add_eq_zero_left (Nat.eq_zero_of_le_zero h_sum)]
      simp [nat_valuation]
    | succ n ih =>
      intro c d h_sum
      cases c with
      | zero => simp [nat_valuation]
      | succ c => cases d with
        | zero => simp [nat_valuation]
        | succ d =>
          match Nat.le.dest (Nat.succ_le_of_lt prime.left) with
          | ⟨q, hq⟩ =>
            rw [(show Nat.succ 1 = 2 by rfl), Nat.add_comm] at hq
            simp only [←hq, (show c.succ * d.succ = (c * d + c + d).succ
              by simp [Nat.succ_mul, Nat.mul_succ, Nat.add_succ]), nat_valuation]
            simp only [hq, (show c * d + c + d + 1 = (c + 1) * (d + 1) by ring)]
            cases Nat.eq_zero_or_pos ((c + 1) * (d + 1) % p) with
            | inl h =>
              rw [if_neg (not_not_intro h)]
              cases prime.2 (c+1) (d+1) h with
              | inl h' =>
                rw [if_neg (not_not_intro h'), ←hq, ←nat_val_succ q d, hq, succ_add]
                have sum_le_n : (c + 1) / p + (d + 1) ≤ n := by
                  apply Nat.le_of_lt_succ
                  apply lt_of_lt_of_le _ h_sum
                  apply Nat.add_lt_add_right
                  apply Nat.div_lt_self _ prime.1
                  rw [Nat.add_comm]
                  apply Nat.lt_add_right 0 1 c (Nat.lt_succ_self 0)
                rw [←ih ((c + 1) / p) (d + 1) sum_le_n]
                have mul_div_assoc : (c + 1) * (d + 1) / p = (c + 1) / p * (d + 1) := by
                  apply nat_mul_left_cancel p _ _ (ne_of_gt (Nat.lt_trans (Nat.lt_succ_self 0) prime.1))
                  rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h), ←mul_assoc,
                    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h')]
                rw [mul_div_assoc]
              | inr h' =>
                rw [if_neg (not_not_intro h'), ←hq, ←nat_val_succ q c, hq, add_succ]
                have sum_le_n : (c + 1) + (d + 1) / p ≤ n := by
                  apply Nat.le_of_lt_succ
                  apply lt_of_lt_of_le _ h_sum
                  apply Nat.add_lt_add_left
                  apply Nat.div_lt_self _ prime.1
                  rw [Nat.add_comm]
                  apply Nat.lt_add_right 0 1 d (Nat.lt_succ_self 0)
                rw [←ih (c + 1) ((d + 1) / p) sum_le_n]
                have mul_div_assoc : (c + 1) * (d + 1) / p = (c + 1) * ((d + 1) / p) := by
                  apply nat_mul_left_cancel p _ _ (ne_of_gt (Nat.lt_trans (Nat.lt_succ_self 0) prime.1))
                  rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h), ←mul_assoc, mul_comm p,
                    mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h')]
                rw [mul_div_assoc]
            | inr h =>
              have hc := ndiv_mul_left _ _ _ (ne_of_gt h)
              have hd := ndiv_mul_right _ _ _ (ne_of_gt h)
              rw [if_pos (ne_of_gt h), if_pos hc, if_pos hd]
              simp
  apply general (a + b) a b (le_refl _)

lemma int_val_mul_eq_add (p : ℕ) (prime : nat_prime p) (a b : ℤ) :
  int_val p (a * b) = int_val p a + int_val p b := by
  simp [int_val, natAbs_mul]
  exact nat_val_mul_eq_add p prime (natAbs a) (natAbs b)


lemma nat_val_add_ge_min (p a b : ℕ) : nat_valuation p (a + b) ≥ min (nat_valuation p a) (nat_valuation p b) := by sorry

lemma natAbs_add (a b : ℤ) : natAbs (a + b) = max (natAbs a) (natAbs b) - min (natAbs a) (natAbs b) := by sorry

lemma int_val_add_ge_min (p : ℕ) (a b : ℤ) : int_val p (a + b) ≥ min (int_val p a) (int_val p b) := by
  simp [int_val, natAbs_add]
  -- exact nat_val_add_ge_min p (natAbs a) (natAbs b)
  sorry

lemma int_val_add_eq_min (p : ℕ) (a b : ℤ) (h : int_val p a < int_val p b) :
  int_val p (a + b) = int_val p a := by sorry

lemma int_val_eq_top_iff_zero (p : ℕ) (gt1 : 1 < p) (a : ℤ) : int_val p a = ∞ ↔ a = 0 := by sorry

def primeVal {p : ℕ} (hp : nat_prime p) : SurjVal (p : ℤ) := {
  v := int_val p,
  v_uniformizer := int_val_uniformizer hp.left,
  v_mul_eq_add_v := int_val_mul_eq_add p hp,
  v_add_ge_min_v := int_val_add_ge_min p,
  v_eq_top_iff_zero := int_val_eq_top_iff_zero p hp.left }

def decr_val_p (p : ℕ) (val : ℤ → ℕ∪∞) (k : ℤ) : ℤ :=
  match val k with
  | 0 => k
  | _ => k / p

lemma zero_valtn_decr_p {p: ℕ} {k : ℤ} (val : ℤ → ℕ∪∞) (h : val k = 0) : decr_val_p p val k = k :=
by rw [decr_val_p, h]

def norm_repr_p (p : ℕ) (x : ℤ) : ℤ := (x % (p : ℤ) + p) % (p : ℤ)

def primeEVR {p : ℕ} (hp : nat_prime p) : EnatValRing (p : ℤ) := {
  valtn := primeVal hp,
  decr_val := decr_val_p p (primeVal hp).v,
  zero_valtn_decr := zero_valtn_decr_p (primeVal hp).v,
  pos_valtn_decr := sorry,
  residue_char := p,
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
  let v_p := (primeEVR hp).valtn.v
  v_p a = 0 ∧ v_p (b ^ 2 - 4 * a * c) > 0

def double_root (a b c : ℤ) (p : ℕ) :=
  -- dbg_trace (a,b,c)
  if p = 2 then
    modulo c 2
  else
    modulo (-b * inv_mod (2 * a) p) p

lemma val_poly_of_double_root {p : ℕ} (hp : nat_prime p) (a b c : ℤ)
  (H : has_double_root a b c hp) :
  (primeEVR hp).valtn.v (a * (double_root a b c p)^2 + b * (double_root a b c p) + c) > 0 ∧
  (primeEVR hp).valtn.v (2*a*(double_root a b c p) + b) > 0 := by sorry



end Int
