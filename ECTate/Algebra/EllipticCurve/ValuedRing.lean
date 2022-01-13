import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Order
import Mathlib.Algebra.Ring.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Lemmas
import Mathlib.Data.Nat.Enat
import Mathlib.Data.Int.Basic

--class ValueMonoid (A : Type u) extends AddCommMonoid A, LinearOrder A

section Obvious

lemma lt_mod_eq_self (n : ℕ) {m : ℕ} (h : m < n) : m % n = m := by sorry

end Obvious


open Enat

structure NormalizedAddValuation {R : Type u} (p : R) [CommRing R] where
  v : R → ℕ∪∞
  v_uniformizer : v p = ofN 1
  v_mul_eq_add_v (a b : R) : v (a * b) = v a + v b
  v_add_ge_min_v (a b : R) : v (a + b) ≥ min (v a) (v b)
  v_eq_top_iff_zero (a : R) : v a = ∞ ↔ a = 0

variable {R : Type u} [CommRing R]

def nat_of_val {p : R} (nav : NormalizedAddValuation p) (a : R) (h : a ≠ 0) : ℕ :=
  match nav.v a with
  | ∞ =>
    by apply False.elim; apply h; rw [←nav.v_eq_top_iff_zero a]; sorry
  | ofN n => n

def lt_val {p : R} (nav : NormalizedAddValuation p) (n : ℕ) (x : R) : Prop := ofN n < nav.v x

instance {p : R} (nav : NormalizedAddValuation p) (n : ℕ) (x : R) : Decidable ((lt_val nav n x) : Prop) := by sorry

lemma lt_val_add {p : R} (nav : NormalizedAddValuation p) (n : ℕ) (a b : R) (ha : lt_val nav n a) (hb : lt_val nav n b) : lt_val nav n (a + b) :=
  by sorry

lemma lt_val_mul_left {p : R} (nav : NormalizedAddValuation p) (a b : R) (ha : lt_val nav n a) : lt_val nav n (a * b) :=
  by sorry

lemma lt_val_mul_right {p : R} (nav : NormalizedAddValuation p) (a b : R) (hb : lt_val nav n b) : lt_val nav n (a * b) :=
  by sorry

class DiscretelyValuedRing {R : Type u} (p : R) extends IntegralDomain R where
  valtn : NormalizedAddValuation p
  decr_val : R → R
  zero_valtn_decr {x : R} (h : valtn.v x = 0) : decr_val x = x
  pos_valtn_decr {x : R} (h : valtn.v x > 0) : x = p * decr_val x

def sub_val {R : Type u} {p : R} (dvr : DiscretelyValuedRing p) (x : R) (n : ℕ) : R :=
  match n, dvr.valtn.v x with
  | 0, _ => x
  | _, 0 => x
  | Nat.succ n, _ => sub_val dvr (dvr.decr_val p x) n

lemma sub_val_lt {R : Type u} {p : R} (dvr : DiscretelyValuedRing p) {x : R} {n m : ℕ} (valx : dvr.valtn.v x = ofN m) (h : m < n) : sub_val dvr x n = sub_val dvr x m := by sorry

lemma sub_val_ge {R : Type u} {p : R} (dvr : DiscretelyValuedRing p) {x : R} {n m : ℕ} (h : dvr.valtn.v x ≥ ofN n) : x = p ^ n * sub_val dvr x n := by sorry

def nat_prime (p : ℕ) : Prop := 1 < p ∧ (∀ a b : ℕ, (a * b) % p = 0 → a % p = 0 ∨ b % p = 0)

def fmul_eq_addf {R R' : Type u} [Mul R] [Add R'] (f : R → R') (x y : R) : Prop := f (x * y) = f x + f y

namespace Int

lemma natAbs_mul (a b : ℤ) : natAbs (a * b) = natAbs a * natAbs b := by sorry

def nat_valuation : ℕ → ℕ → ℕ∪∞
  | p, 0 => ∞
  | 0, (m+1) => ofN 0
  | 1, (m+1) => ∞
  | (q+2), (m+1) => if (m+1) % (q+2) ≠ 0 then ofN 0 else succ (nat_valuation (q+2) ((m+1) / (q+2)))
termination_by
  measure (fun ⟨p, k⟩ => k)
decreasing_by
  simp only [measure, invImage, InvImage, Nat.lt_wfRel]
  apply Nat.div_lt_self
  . exact Nat.zero_lt_succ m
  . exact Nat.succ_lt_succ (Nat.zero_lt_succ q)

lemma nat_val_zero (p : ℕ) : nat_valuation p 0 = ∞ := by sorry
lemma nat_val_succ (q m : ℕ) : nat_valuation (q+2) (m+1) = if (m+1) % (q+2) ≠ 0 then ofN 0 else succ (nat_valuation (q+2) ((m+1) / (q+2))) := by rfl

lemma induction_nat_val_mul (p a b : ℕ) (h : nat_prime p) : (∀ (a' b' : ℕ), a' * b' <  a * b → fmul_eq_addf (nat_valuation p) a' b') → fmul_eq_addf (nat_valuation p) a b := by sorry

def int_val (p : ℕ) (k : ℤ) : ℕ∪∞ :=
  nat_valuation p (natAbs k)

lemma int_val_uniformizer {p : ℕ} (gt1 : 1 < p) : int_val p p = ofN 1 := by
  delta int_val
  rw [natAbs_ofNat]
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

lemma int_val_eq_top_iff_zero (p : ℕ) (gt1 : 1 < p) (a : ℤ) : int_val p a = ∞ ↔ a = 0 := by sorry

def primeVal {p : ℕ} (hp : nat_prime p) : NormalizedAddValuation (ofNat p) := {
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

def primeDVR {p : ℕ} (hp : nat_prime p) : DiscretelyValuedRing (p : ℤ) := {
  valtn := primeVal hp,
  decr_val := decr_val_p p (primeVal hp).v,
  zero_valtn_decr := zero_valtn_decr_p (primeVal hp).v,
  pos_valtn_decr := sorry
}


end Int
