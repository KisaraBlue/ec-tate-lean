import Mathlib.Algebra.EllipticCurve.Kronecker
import Mathlib.Algebra.EllipticCurve.Model
import Mathlib.Algebra.EllipticCurve.ValuedRing
import Mathlib.Data.Nat.Enat
import Mathlib.Init.Data.Int.Basic



lemma prime_p (p : ℕ) : nat_prime p := sorry


open Enat

inductive Kodaira where
  | I     : Nat → Kodaira --for both I0 and In with n > 0
  | II    : Kodaira
  | III   : Kodaira
  | IV    : Kodaira
  | Is    : Nat → Kodaira
  | IIs   : Kodaira
  | IIIs  : Kodaira
  | IVs   : Kodaira

open Kodaira

instance : Repr Kodaira where
  reprPrec
    | I m, _   => "I" ++ repr m
    | II, _    => "II"
    | III, _   => "III"
    | IV, _    => "IV"
    | Is m, _  => "I*" ++ repr m
    | IIs, _   => "II*"
    | IIIs, _  => "III*"
    | IVs, _   => "IV*"

lemma eq_I_Nat (m n : Nat) : m = n ↔ I m = I n := by
  apply Iff.intro
  intro h
  exact congrArg I h
  intro h
  cases h
  rfl

lemma eq_Is_Nat (m n : Nat) : m = n ↔ Is m = Is n := by
  apply Iff.intro
  intro h
  exact congrArg Is h
  intro h
  cases h
  rfl

instance : DecidableRel ((. = . ) : Kodaira → Kodaira → Prop) :=
fun k k' => match k, k' with
  | I n, I n' => decidable_of_decidable_of_iff inferInstance (eq_I_Nat n n')
  | II, II => isTrue rfl
  | III, III => isTrue rfl
  | IV, IV => isTrue rfl
  | Is n, Is n' => decidable_of_decidable_of_iff inferInstance (eq_Is_Nat n n')
  | IIs, IIs => isTrue rfl
  | IIIs, IIIs => isTrue rfl
  | IVs, IVs => isTrue rfl
--| k, k' => isFalse (@Kodaira.noConfusion _ k k')
  | I n, II => isFalse Kodaira.noConfusion
  | I n, III => isFalse Kodaira.noConfusion
  | I n, IV => isFalse Kodaira.noConfusion
  | I n, Is n' => isFalse Kodaira.noConfusion
  | I n, IIs => isFalse Kodaira.noConfusion
  | I n, IIIs => isFalse Kodaira.noConfusion
  | I n, IVs => isFalse Kodaira.noConfusion
  | II, I n => isFalse Kodaira.noConfusion
  | II, III => isFalse Kodaira.noConfusion
  | II, IV => isFalse Kodaira.noConfusion
  | II, Is n' => isFalse Kodaira.noConfusion
  | II, IIs => isFalse Kodaira.noConfusion
  | II, IIIs => isFalse Kodaira.noConfusion
  | II, IVs => isFalse Kodaira.noConfusion
  | III, I n => isFalse Kodaira.noConfusion
  | III, II => isFalse Kodaira.noConfusion
  | III, IV => isFalse Kodaira.noConfusion
  | III, Is n' => isFalse Kodaira.noConfusion
  | III, IIs => isFalse Kodaira.noConfusion
  | III, IIIs => isFalse Kodaira.noConfusion
  | III, IVs => isFalse Kodaira.noConfusion
  | IV, I n => isFalse Kodaira.noConfusion
  | IV, II => isFalse Kodaira.noConfusion
  | IV, III => isFalse Kodaira.noConfusion
  | IV, Is n' => isFalse Kodaira.noConfusion
  | IV, IIs => isFalse Kodaira.noConfusion
  | IV, IIIs => isFalse Kodaira.noConfusion
  | IV, IVs => isFalse Kodaira.noConfusion
  | Is n, II => isFalse Kodaira.noConfusion
  | Is n, III => isFalse Kodaira.noConfusion
  | Is n, IV => isFalse Kodaira.noConfusion
  | Is n, I n' => isFalse Kodaira.noConfusion
  | Is n, IIs => isFalse Kodaira.noConfusion
  | Is n, IIIs => isFalse Kodaira.noConfusion
  | Is n, IVs => isFalse Kodaira.noConfusion
  | IIs, I n => isFalse Kodaira.noConfusion
  | IIs, III => isFalse Kodaira.noConfusion
  | IIs, IV => isFalse Kodaira.noConfusion
  | IIs, Is n' => isFalse Kodaira.noConfusion
  | IIs, II => isFalse Kodaira.noConfusion
  | IIs, IIIs => isFalse Kodaira.noConfusion
  | IIs, IVs => isFalse Kodaira.noConfusion
  | IIIs, I n => isFalse Kodaira.noConfusion
  | IIIs, II => isFalse Kodaira.noConfusion
  | IIIs, IV => isFalse Kodaira.noConfusion
  | IIIs, Is n' => isFalse Kodaira.noConfusion
  | IIIs, IIs => isFalse Kodaira.noConfusion
  | IIIs, III => isFalse Kodaira.noConfusion
  | IIIs, IVs => isFalse Kodaira.noConfusion
  | IVs, I n => isFalse Kodaira.noConfusion
  | IVs, II => isFalse Kodaira.noConfusion
  | IVs, III => isFalse Kodaira.noConfusion
  | IVs, Is n' => isFalse Kodaira.noConfusion
  | IVs, IIs => isFalse Kodaira.noConfusion
  | IVs, IIIs => isFalse Kodaira.noConfusion
  | IVs, IV => isFalse Kodaira.noConfusion
--treat all false cases at once?



namespace ValidModel

variable (R : Type u) [CommRing R]

def val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) : ℕ := nat_of_val valp e.discr_not_zero

lemma iso_rst_val_discr_to_nat {p : R} (valp : SurjVal p) (r s t : R) (e : ValidModel R) : val_discr_to_nat R valp (rst_iso r s t e) = val_discr_to_nat R valp e := by sorry

lemma ofN_val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) : ofN (val_discr_to_nat R valp e) = valp.v e.discr := by
  delta val_discr_to_nat
  delta nat_of_val
  cases valp.v e.discr with
  | ofN n => simp
  | top => sorry

lemma v_b2_of_v_a1_a2 {p : R} (valp : SurjVal p) (e : ValidModel R) (h1 : valp.v e.a1 ≥ ofN 1) (h2 : valp.v e.a2 = ofN 1) : valp.v e.b2 ≥ ofN 1 :=
  val_add_ge_of_ge valp (val_mul_ge_of_left_ge valp h1) (val_mul_ge_of_right_ge valp (le_of_eq h2.symm))


lemma v_b4_of_v_a1_a3_a4 {p : R} (valp : SurjVal p) (e : ValidModel R) (h1 : valp.v e.a1 ≥ ofN 1) (h3 : valp.v e.a3 ≥ ofN q) (h4 : valp.v e.a4 ≥ ofN (q + 1)) : valp.v e.b4 ≥ ofN (q + 1) := by
  apply val_add_ge_of_ge valp
  . rw [←add_ofN, Enat.add_comm]
    exact (val_mul_ge_of_both_ge valp h1 h3)
  . exact (val_mul_ge_of_right_ge valp h4)

lemma v_b6_of_v_a3_a6 {p : R} (valp : SurjVal p) (e : ValidModel R) (h3 : valp.v e.a3 ≥ ofN q) (h6 : valp.v e.a6 ≥ ofN (2 * q)) : valp.v e.b6 ≥ ofN (2 * q) := by
  apply val_add_ge_of_ge valp
  . rw [←add_self_eq_mul_two q]
    exact (val_mul_ge_of_both_ge valp h3 h3)
  . exact (val_mul_ge_of_right_ge valp h6)

lemma v_b8_of_v_ai {p : R} (valp : SurjVal p) (e : ValidModel R) (h1 : valp.v e.a1 ≥ ofN 1) (h2 : valp.v e.a2 = ofN 1) (h3 : valp.v e.a3 ≥ ofN q) (h4 : valp.v e.a4 ≥ ofN (q + 1)) (h6 : valp.v e.a6 ≥ ofN (2 * q)) : valp.v e.b8 ≥ ofN (2 * q + 1) := by
  simp [Model.b8]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  repeat apply val_add_ge_of_ge valp
  . rw [mul_assoc, Nat.add_comm, ←add_ofN]
    exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h1 h6)
  . rw [val_of_neg, mul_assoc, ←add_self_eq_mul_two q, Nat.add_assoc, ←add_ofN]
    exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h3 h4)
  . rw [mul_assoc, Nat.add_comm, ←add_ofN]
    exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp (le_of_eq h2.symm) h6)
  . rw [mul_assoc, ←add_self_eq_mul_two q, Nat.add_comm, ←add_ofN, ←add_ofN]
    exact val_mul_ge_of_both_ge valp (le_of_eq h2.symm) (val_mul_ge_of_both_ge valp h3 h3)
  . rw [val_of_neg, ←add_self_eq_mul_two q, Nat.add_assoc, ←add_ofN]
    exact val_mul_ge_of_both_ge valp (Enat.le_trans (le_succ (ofN q)) h4) h4


lemma v_discr_of_v_ai {p : R} (valp : SurjVal p) (e : ValidModel R) (hq : q > 1) (h1 : valp.v e.a1 ≥ ofN 1) (h2 : valp.v e.a2 = ofN 1) (h3 : valp.v e.a3 ≥ ofN q) (h4 : valp.v e.a4 ≥ ofN (q + 1)) (h6 : valp.v e.a6 ≥ ofN (2 * q)) : valp.v e.discr ≥ ofN (2 * q + 3) := by
  have h2' := v_b2_of_v_a1_a2 R valp e h1 h2
  have h4' := v_b4_of_v_a1_a3_a4 R valp e h1 h3 h4
  have h6' := v_b6_of_v_a3_a6 R valp e h3 h6
  have h8' := v_b8_of_v_ai R valp e h1 h2 h3 h4 h6
  simp [Model.discr]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply val_add_ge_of_ge valp
  . apply val_add_ge_of_ge valp
    . apply val_add_ge_of_ge valp
      . rw [←neg_mul_left, ←neg_mul_left, val_of_neg, (show 3 = 1 + 1 + 1 by rfl), ←Nat.add_assoc, ←Nat.add_assoc, Nat.add_assoc, mul_comm, ←add_ofN]
        exact val_mul_ge_of_both_ge valp h8' (val_mul_ge_of_both_ge valp h2' h2')
      . rw [val_of_neg, pow_succ, pow_succ, pow_one, (show 2 * q + 3 = q + 1 + (q + 1) + 1 by ring), ←add_ofN, ←add_ofN]
        exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp (val_mul_ge_of_both_ge valp h4' h4') (Enat.le_trans ((le_ofN _ _).1 (Nat.le_add_left 1 q)) h4'))
    . rw [val_of_neg, ←add_ofN, mul_assoc, (show 3 = 2 + 1 by rfl)]
      apply val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h6' (Enat.le_trans ((le_ofN _ _).1 _) h6'))
      rw [←add_self_eq_mul_two q]
      exact Nat.add_le_add (Nat.succ_le_of_lt hq) (Nat.le_of_lt hq)
  . rw [(show 3 = 1 + (1 + 1) by rfl), ←add_ofN, ←add_ofN, mul_comm, mul_assoc 9]
    exact val_mul_ge_of_both_ge valp h6' (val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h2' (Enat.le_trans ((le_ofN _ _).1 (Nat.add_le_add (Nat.le_of_lt hq) (le_of_eq rfl))) h4')))





end ValidModel

open ValidModel

namespace Int

def count_roots_cubic_aux (a b c d : ℤ) (p : ℕ) (x : ℕ) : ℕ := match x with
  | Nat.zero => if d = 0 then 1 else 0
  | Nat.succ x' => (if (a * (x^3 : ℕ) + b * (x^2 : ℕ) + c * x + d) % (p : ℤ) = 0 then 1 else 0) + count_roots_cubic_aux a b c d p x'

def count_roots_cubic (a b c d : ℤ) (p : ℕ) : ℕ :=
  count_roots_cubic_aux (modulo a p) (modulo b p) (modulo c p) (modulo d p) p (p - 1)

def tate_big_prime (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) : Kodaira × ℕ × ℕ × (ℤ × ℤ × ℤ × ℤ) :=
  let evrp := primeEVR hp
  let navp := evrp.valtn
  let valp := navp.v
  let c4 := e.c4
  let c6 := e.c6
  let Δ := e.discr
  let n := val_discr_to_nat ℤ navp e
  let ⟨vpj, k, integralInv⟩ := match valp (c4 ^ 3) with
    | ∞ => (0, n, true)
    | ofN v_c4_3 => if v_c4_3 < n then ((v_c4_3 : ℤ) - (n : ℤ), v_c4_3, false) else (v_c4_3 - n, n, true)
  let ⟨u, r, s, t⟩ :=
    if k < 12 then (1, 0, 0, 0) else
    let u' := p ^ (k / 12)
    let s' := if modulo e.a1 2 = 1
      then (u' - e.a1) / 2
      else - e.a1 / 2
    let a2' := e.a2 - s' * e.a1 - s' * s'
    let r' := if a2' % 3 = 0
      then - a2' / 3
      else if a2' % 3 = 1
        then (u' * u' - a2') / 3
        else - (u' * u' + a2') / 3
    let a3' := e.a3 + r' * e.a1
    let t' := if a3' % 2 = 1
      then (u' * u' * u' - a3')/2
      else -a3' / 2
    (u', r', s', t')
  let k := k % 12
  let Δ := Δ / ofNat (u ^ 12)
  let c6 := c6 / ofNat (u ^ 6)
  let c4 := c4 / ofNat (u ^ 4)
  if not integralInv then
    let ν := natAbs vpj
    match k with
      | 0 => (I ν, 1,
        if kronecker (-c6) p = 1 then ν else gcd 2 ν,
        (u, r, s, t))
      | 6 => (Is ν, 2,
        natAbs (3 + kronecker (if ν % 2 = 1 then (Δ * c6 / p ^ (ν + 9)) else (Δ / p ^ (ν + 6))) p),
        (u, r, s, t))
      | _ => (I 0, 0, 0, (0, 0, 0, 0))
  else
    match k with
      | 0  => (I 0,  0, 1, (u, r, s, t))
      | 2  => (II,   2, 1, (u, r, s, t))
      | 3  => (III,  2, 2, (u, r, s, t))
      | 4  => (IV,   2,
        natAbs (2 + kronecker (-6 * c6 / (p * p)) p),
        (u, r, s, t))
      | 6  => (Is 0, 2,
        1 + count_roots_cubic 4 0 (-3*c4 / (p*p)) (-c6 / (p*p*p)) p,
      (u, r, s, t))
      | 8  => (IVs,  2,
        natAbs (2 + kronecker (-6 * c6 / (p ^ 4 : ℕ)) p),
        (u, r, s, t))
      | 9  => (IIIs, 2, 2, (u, r, s, t))
      | 10 => (IIs,  2, 1, (u, r, s, t))
      | _  => (I 0, 0, 0, (0, 0, 0, 0))
set_option profiler true

open ValidModel


unsafe
def kodaira_type_Is (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) (u0 r0 s0 t0 : ℤ) (m q : ℕ)
  (hq : 1 < q) (h1 : (primeEVR hp).valtn.v e.a1 ≥ ofN 1) (h2 : (primeEVR hp).valtn.v e.a2 = ofN 1) (h3 : (primeEVR hp).valtn.v e.a3 ≥ ofN q) (h4 : (primeEVR hp).valtn.v e.a4 ≥ ofN (q + 1)) (h6 : (primeEVR hp).valtn.v e.a6 ≥ ofN (2 * q)) : ℕ × ℕ × ℤ × ℤ :=
  let evrp := primeEVR hp
  let navp := evrp.valtn
  let valp := navp.v
  let (r, t) := (r0, t0)
  let a3q := sub_val evrp e.a3 q
  let a6q2 := sub_val evrp e.a6 (2 * q)
  --obvious rewriting lemmas that Lean should generate implicitely
  have rw_a3 : sub_val evrp e.a3 q = a3q := rfl
  have rw_a6 : sub_val evrp e.a6 (2 * q) = a6q2 := rfl

  if discr_1 : valp (a3q ^ 2 + 4 * a6q2) = 0 then
    let c := if quad_root_in_ZpZ 1 a3q (-a6q2) p then 4 else 2;
    (m, c, (r, t))
  else
  have hdr : has_double_root 1 a3q (-a6q2) hp := by
    apply And.intro (val_of_one navp) _
    apply pos_of_ne_zero
    rw [mul_one, ←neg_mul_right, sub_eq_add_neg, neg_neg]
    assumption;
  let a := double_root 1 a3q (-a6q2) p
  let rw_a : double_root 1 a3q (-a6q2) p = a := rfl
  --if p = 2 then modulo a6q2 2 else modulo (2 * -a3q) 3;
  let e' := rst_iso 0 0 (a * p ^ q) e;
  have h1' : valp e'.a1 ≥ ofN 1 := by
    simp [rst_iso, Model.rst_iso, Model.iso]
    assumption;
  have h2' : valp e'.a2 = ofN 1 := by
    simp [rst_iso, Model.rst_iso, Model.iso]
    assumption;
  have h3' : valp e'.a3 ≥ ofN (q+1) := by
    simp [rst_iso, Model.rst_iso, Model.iso]
    rw [factor_p_of_le_val evrp h3, ofNat_pow, ←mul_assoc, mul_comm _ (ofNat p ^ q), ←mul_add, navp.v_mul_eq_add_v, val_of_pow_uniformizer, ←add_ofN]
    apply add_le_add (le_of_eq rfl)
    rw [←succ_ofN, Int.add_comm, ←mul_one 2, rw_a3, rw_a6, sub_val_p_mul]
    exact succ_le_of_lt (val_poly_of_double_root hp 1 a3q (-a6q2) hdr).2;
  have h4' : valp e'.a4 ≥ ofN (q+1) := by
    simp [rst_iso, Model.rst_iso, Model.iso]
    apply Enat.le_trans _ (navp.v_add_ge_min_v _ _)
    apply le_min h4
    rw [mul_assoc, val_of_neg, navp.v_mul_eq_add_v, Enat.add_comm, navp.v_mul_eq_add_v, ofNat_pow, val_of_pow_uniformizer, ←add_ofN]
    apply Enat.le_trans _ (le_add_right (ofN q + navp.v e.toModel.a1) _)
    exact add_le_add (le_of_eq rfl) h1;
  have h6' : (primeEVR hp).valtn.v e'.a6 ≥ ofN (2 * q + 1) := by
    simp [rst_iso, Model.rst_iso, Model.iso, rw_a3, rw_a6]
    rw [factor_p_of_le_val evrp h6, factor_p_of_le_val evrp h3, rw_a6, rw_a3, ofNat_pow, ←val_of_neg, sub_eq_add_neg, neg_add, neg_neg, Int.add_comm, neg_mul_right, rw_a,
      (show a * ofNat p ^ q * (ofNat p ^ q * a3q + a * ofNat p ^ q) = ofNat p ^ q * ofNat p ^ q * ((a + a3q) * a) by ring),
      ←pow_add (ofNat p), add_self_eq_mul_two, ←mul_add, navp.v_mul_eq_add_v, val_of_pow_uniformizer, ←add_ofN, add_mul, mul_self_eq_square, ←one_mul (a ^ 2)]
    exact add_le_add (le_of_eq rfl) (succ_le_of_lt (val_poly_of_double_root hp 1 a3q (-a6q2) hdr).1);
  let t := t + u0 ^ 3 * a * p ^ q;
  let a2p := sub_val evrp e'.a2 1
  let a4pq := sub_val evrp e'.a4 (q + 1)
  let a6pq2 := sub_val evrp e'.a6 (2 * q + 1)
  --obvious rewriting lemmas that Lean should generate implicitely
  have rw_a2' : sub_val evrp e'.a2 1 = a2p := rfl
  have rw_a4' : sub_val evrp e'.a4 (q + 1) = a4pq := rfl
  have rw_a6' : sub_val evrp e'.a6 (2 * q + 1) = a6pq2 := rfl
  --less obvious lemma
  have rw_a2 : sub_val evrp e.a2 1 = a2p := by
    simp [←rw_a2', rst_iso, Model.rst_iso, Model.iso];

  if discr_2 : valp (a4pq ^ 2 - 4 * a2p * a6pq2) = 0 then
    let c := if quad_root_in_ZpZ a2p a4pq a6pq2 p then 4 else 2;
    (m + 1, c, (r, t))
  else
  have hdr' : has_double_root a2p a4pq a6pq2 hp := by
    have v_a2p : valp a2p = 0 := by
      rw [←rw_a2', factor_p_of_eq_val evrp h2', sub_val_p_mul]
      simp only [val_sub_val evrp e'.a2 1, h2'];
    apply And.intro v_a2p _
    apply pos_of_ne_zero
    assumption;
  let a' := double_root a2p a4pq a6pq2 p
  have rw_a' : double_root a2p a4pq a6pq2 p = a' := rfl
  --if p = 2 then modulo a6pq2 2 else modulo (2 * a2p * -a4pq) 3;
  let e'' := rst_iso (a' * p ^ q) 0 0 e';
  have rst_iso_a4' : e.toModel.a4 - a * ofNat p ^ q * e.toModel.a1 = e'.toModel.a4 := by simp [rst_iso, Model.rst_iso, Model.iso, rw_a3, rw_a6, ofNat_pow]
  have h1'' : valp e''.a1 ≥ ofN 1 := by
    simp [rst_iso, Model.rst_iso, Model.iso]
    assumption;
  have h2'' : valp e''.a2 = ofN 1 := by
    simp only [rst_iso, Model.rst_iso, Model.iso, one_pow, one_mul, zero_mul, sub_zero, mul_zero, Int.add_zero]
    rw [v_add_eq_min_v navp]
    . assumption
    . rw [h2, navp.v_mul_eq_add_v, Enat.add_comm, navp.v_mul_eq_add_v, Enat.add_comm _ (navp.v (ofNat (p ^ q))), Enat.add_assoc, ofNat_pow, val_of_pow_uniformizer navp]
      rw [lt_ofN 1 q] at hq
      apply lt_of_lt_of_le hq (le_add_right (ofN q) _);
  have h3'' : valp e''.a3 ≥ ofN (q + 1) := by
    simp [rst_iso, Model.rst_iso, Model.iso]
    apply Enat.le_trans _ (navp.v_add_ge_min_v _ _)
    simp [rst_iso, Model.rst_iso, Model.iso] at h3'
    apply le_min h3'
    rw [mul_assoc, navp.v_mul_eq_add_v, Enat.add_comm, navp.v_mul_eq_add_v, ofNat_pow, val_of_pow_uniformizer, ←add_ofN]
    apply Enat.le_trans _ (le_add_right (ofN q + navp.v e.toModel.a1) _)
    exact add_le_add (le_of_eq rfl) h1;
  have h4'' : valp e''.a4 ≥ ofN (q + 2) := by
    simp [rst_iso, Model.rst_iso, Model.iso, rw_a4', rw_a6', rw_a3, rw_a6]
    simp [rst_iso, Model.rst_iso, Model.iso, rw_a3, rw_a6, rw_a] at h4';
    rw [rw_a2, factor_p_of_le_val evrp h4', ofNat_pow, rst_iso_a4', rw_a4', factor_p_of_le_val evrp (le_of_eq h2.symm), rw_a2, rw_a',
      (show 2 * (a' * ofNat p ^ q) * (ofNat p ^ 1 * a2p) = ofNat p ^ q  * ofNat p ^ 1  * (2 * a2p * a') by ring),
      ←pow_add (ofNat p), ←mul_add, Int.add_comm a4pq]
    apply Enat.le_trans (le_min _ _) (navp.v_add_ge_min_v _ _)
    . rw [(show q + 2 = q + 1 + 1 by rfl), navp.v_mul_eq_add_v, val_of_pow_uniformizer, ←add_ofN]
      exact add_le_add (le_of_eq rfl) (succ_le_of_lt (val_poly_of_double_root hp a2p a4pq a6pq2 hdr').2)
    . rw [(show 3 * (a' * ofNat p ^ q) * (a' * ofNat p ^ q) = ofNat p ^ q * ofNat p ^ q * (3 * a' * a') by ring), ←pow_add (ofNat p)]
      apply val_mul_ge_of_left_ge navp _
      rw [val_of_pow_uniformizer]
      exact (le_ofN _ _).1 (Nat.add_le_add (le_of_eq rfl) (Nat.succ_le_of_lt hq));
  have h6'' : valp e''.a6 ≥ ofN (2 * (q + 1)) := by
    simp [rst_iso, Model.rst_iso, Model.iso, rw_a4', rw_a6', rw_a3, rw_a6]
    simp [rst_iso, Model.rst_iso, Model.iso, rw_a3, rw_a6, rw_a] at h6';
    rw [rw_a2, factor_p_of_le_val evrp h6', rw_a,
      (show e.toModel.a6 - a * ofNat (p ^ q) * (e.toModel.a3 + a * ofNat (p ^ q)) = e'.toModel.a6 by simp [rst_iso, Model.rst_iso, Model.iso, rw_a3, rw_a6]), rw_a6', rw_a', ofNat_pow]
    apply val_add_ge_of_ge navp _ _
    . rw [rst_iso_a4', factor_p_of_le_val evrp h4', factor_p_of_le_val evrp (le_of_eq h2.symm), rw_a4', rw_a2,
      (show ofNat p ^ (2 * q + 1) * a6pq2 + a' * ofNat p ^ q * (ofNat p ^ (q + 1) * a4pq) + a' * ofNat p ^ q * (a' * ofNat p ^ q) * (ofNat p ^ 1 * a2p) = ofNat p ^ q * ofNat p ^ q * ofNat p ^ 1 * (a2p * (a' * a')) + ofNat p ^ q * ofNat p ^ (q + 1) * (a4pq * a') + ofNat p ^ (2 * q + 1) * a6pq2 by sorry),
      ←pow_add (ofNat p), ←pow_add (ofNat p), ←pow_add (ofNat p), ←Nat.add_assoc, (show q + q + 1 = 2 * q + 1 by rw [add_self_eq_mul_two]), ←mul_add, ←mul_add, (show 2 * (q + 1) = 2 * q + 1 + 1 by ring), ←add_ofN, navp.v_mul_eq_add_v, val_of_pow_uniformizer, mul_self_eq_square]
      exact add_le_add (le_of_eq rfl) (succ_le_of_lt (val_poly_of_double_root hp a2p a4pq a6pq2 hdr').1)
    . rw [(show a' * ofNat p ^ q * (a' * ofNat p ^ q) * (a' * ofNat p ^ q) = a' * ofNat p ^ q * (a' * ofNat p ^ q) * (a' * ofNat p ^ q) by ring)]
      sorry

    ;
  let r := r + u0 ^ 2 + a * p ^ q; let t := t + u0 ^ 2 * s0 * a * p ^ q;
  kodaira_type_Is p hp e'' u0 r s0 t (m + 2) (q + 1) (Nat.lt_succ_of_lt hq) h1'' h2'' h3'' h4'' h6''
termination_by _ =>
  val_discr_to_nat ℤ evrp.valtn e - (2 * q + 3)
--decreasing_by
--  exact v_discr_of_v_ai navp

/-apply Enat.le_trans _ (navp.v_add_ge_min_v _ _)
    apply le_min
    . rw [factor_p_of_le_val evrp h1, factor_p_of_eq_val evrp h2, pow_one, mul_assoc 2, ←mul_assoc _ (ofNat p), ←mul_assoc _ (ofNat p), mul_assoc _ _ (ofNat p), mul_assoc _ _ (ofNat p), ofNat_pow, ←pow_succ, mul_comm _ (ofNat p ^ q.succ), mul_comm _ (ofNat p ^ q.succ), mul_comm 2, mul_assoc (ofNat p ^ q.succ), mul_assoc (ofNat p ^ q.succ), mul_assoc (ofNat p ^ q.succ), sub_eq_add_neg, neg_mul_right, ←mul_add, ←mul_add, navp.v_mul_eq_add_v, val_of_pow_uniformizer, Int.add_comm, mul_assoc _ _ 2, mul_comm _ 2, mul_comm a, ←sub_eq_add_neg, Nat.add_succ, Nat.succ_eq_add_one (q+1), ←add_ofN (q+1), (show (sub_val evrp e.toModel.a4 (q + 1) - double_root 1 a3q (-a6q2) p * sub_val evrp e.toModel.a1 1) = a4pq by sorry), (show sub_val evrp e.toModel.a2 1 = a2p by sorry)]
      apply add_le_add (le_of_eq rfl)
      rw [←succ_ofN]
      apply succ_le_of_lt
      exact (val_poly_of_double_root hp a2p a4pq _ hdr').2
    . rw [←mul_assoc, ←mul_assoc, navp.v_mul_eq_add_v, mul_comm, ←mul_assoc, ←mul_assoc, navp.v_mul_eq_add_v, ofNat_pow, val_of_pow_uniformizer, Enat.add_assoc, Enat.add_comm, ←add_ofN, Enat.add_assoc]
      apply add_le_add (le_of_eq rfl)
      apply Enat.le_trans _ (le_add_right _ _)
      rw [←le_ofN]
      exact Nat.succ_le_of_lt hq-/

unsafe
def tate_small_prime (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) (u0 r0 s0 t0 : ℤ) : Kodaira × ℕ × ℕ × (ℤ × ℤ × ℤ × ℤ) :=
  if smallp : p ≠ 2 ∧ p ≠ 3 then (I 0, 0, 0, (0, 0, 0, 0)) else
  let (u, r, s, t) := (u0, r0, s0, t0);
  let evrp := primeEVR hp; let navp := evrp.valtn; let valp := navp.v;
  let Δ := e.discr; let n := val_discr_to_nat ℤ navp e;
  if n = 0 then (I 0, 0, 1, (u, r, s, t)) else
  if valp e.b2 = 0 then
    let (r1, t1) := if p = 2 then
      (modulo e.a3 2, modulo (e.a3 + e.a4) 2)
    else
      let r1' := modulo (-e.b2 * e.b4) 3;
      (r1', modulo (e.a1 * r1' + e.a3) 3);
    let e := rst_iso r1 0 t1 e;
    let r := r + r1 * u ^ 2;
    let t := t + t1 * u ^ 3 + s * r1 * u ^ 2;
    let c := if quad_root_in_ZpZ 1 e.a1 (-e.a2) p then n else gcd 2 n;
    (I n, 1, c, (u, r, s, t))
  else
  let (r1, s1, t1) := if p = 2 then
    let r1' := modulo e.a4 2; let s1' := modulo (r1' + e.a2) 2;
    (r1', s1', modulo (e.a6 + r1' * (e.a4 + s1')) 2)
  else
    let r1' := modulo (-e.b6) 3;
    (r1', modulo e.a1 3, modulo (e.a3 + r1' * e.a1) 3);
  let e := rst_iso r1 s1 t1 e;
  let (r, s) := (r + r1 * u ^ 2, s + u * s1);
  let t := t + t1 * u ^ 3 + s * r1 * u ^ 2;
  if valp e.a6 < ofN 2 then (II, n, 1, (u, r, s, t)) else
  if valp e.b8 < ofN 3 then (III, n-1, 2, (u, r, s, t)) else
  if valp e.b6 < ofN 3 then
    let (a3p, a6p2) := (sub_val evrp e.a3 1, sub_val evrp e.a6 2);
    let c := if quad_root_in_ZpZ 1 a3p (-a6p2) p then 3 else 1;
    (IV, n - 2, c, (u, r, s, t)) else
  let k := if valp e.a6 < ofN 3 then if p = 2 then 2 else modulo e.a3 9 else 0;
  let e := rst_iso 0 0 k e; let t := t + k * u ^ 3;
  -- have p|a2, p2|a4, p3|a6
  let (a2p, a4p2, a6p3) := (sub_val evrp e.a2 1, sub_val evrp e.a4 2, sub_val evrp e.a6 3);
  -- 18bcd – 4b³d + b²c² – 4c³ – 27d²
  let Δcube := -4 * a2p^3 * a6p3 + a2p^2 * a4p2^2 - 4 * a4p2^3 - 27 * a6p3^2;
  if valp Δcube = 0 then
    let c := 1 + count_roots_cubic 1 a2p a4p2 a6p3 p;
    (Is 0, n - 4, c, (u, r, s, t))
  else
  if valp (3 * a4p2 - a2p ^ 2) = 0 then
    let r1 := p * (modulo (if p = 2 then a4p2 else a2p * a4p2) p);
    let e := rst_iso r1 0 0 e;
    let r := r + u^2 * r1; let t := t + u ^ 2 * s * r1;
    have h1 : valp e.a1 ≥ ofN 1 := sorry;
    have h2 : valp e.a2 = ofN 1 := sorry;
    have h3 : valp e.a3 ≥ ofN 2 := sorry;
    have h4 : valp e.a4 ≥ ofN 3 := sorry;
    have h6 : valp e.a6 ≥ ofN 4 := sorry;
    let (m, c, (r, t)) := kodaira_type_Is p hp e u r s t 1 2 (Nat.lt_succ_self 1) h1 h2 h3 h4 h6;
    (Is m, n - m - 4, c, (u, r, s, t))
  else
  let r1 := p * (modulo (if p = 2 then -a2p else -a6p3) p);
  let e := rst_iso r1 0 0 e;
  let r := r + u^2 * r1; let t := t + u ^ 2 * s * r1;
  -- have p2|a3, p4|a6
  let (a3p2, a6p4) := (sub_val evrp e.a3 2, sub_val evrp e.a6 4);
  if valp (a3p2 ^ 2 + 4 * a6p4) = 0 then
    let c := if quad_root_in_ZpZ 1 a3p2 (-a6p4) p then 3 else 1;
    (IVs, n - 6, c, (u, r, s, t))
  else
  let a := if p = 2 then modulo a6p4 2 else modulo (2 * a3p2) 3;
  let k := -a * (p ^ 2 : ℕ);
  let e := rst_iso 0 0 k e; let t := t + k * u ^ 3;
  if valp e.a4 < ofN 4 then (IIIs, n - 7, 2, (u, r, s, t)) else
  if valp e.a6 < ofN 6 then (IIs, n - 8, 1, (u, r, s, t)) else
  have pnz : p ≠ 0 := (ne_of_lt (lt_trans Nat.zero_lt_one hp.left)).symm;
  tate_small_prime p hp (u_iso (p : ℤ) e) (p * u) r s t

unsafe
def tate_algorithm (p : ℕ) (e : ValidModel ℤ) : Kodaira × ℕ × ℕ × (ℤ × ℤ × ℤ × ℤ) :=
  if p = 2 then
    tate_small_prime 2 (Int.prime_2) e 1 0 0 0
  else if p = 3 then
    tate_small_prime 3 (Int.prime_3) e 1 0 0 0
  else
    tate_big_prime p (prime_p p) e


def test_model : ValidModel ℤ := ⟨ ⟨1, -1, 1, -23130, -1322503⟩ , by simp⟩

end Int
