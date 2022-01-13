import Mathlib.Algebra.EllipticCurve.Kronecker
import Mathlib.Algebra.EllipticCurve.Model
import Mathlib.Algebra.EllipticCurve.ValuedRing
import Mathlib.Data.Nat.Enat
import Mathlib.Data.Int.Basic

lemma prime_2 : nat_prime 2 := by
  simp only [nat_prime, true_and]
  sorry
lemma prime_3 : nat_prime 3 := by
  simp only [nat_prime, true_and]
  sorry

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

namespace ValidModel

variable (R : Type u) [CommRing R]

lemma lt_val_b4 {p : R} (valp : NormalizedAddValuation p) (n : ℕ) (e : ValidModel R) (h13 : lt_val valp n e.a1 ∨ lt_val valp n e.a3) (h4 : lt_val valp n e.a4) : lt_val valp n e.b4 :=
  by sorry

lemma lt_val_b6 {p : R} (valp : NormalizedAddValuation p) (e : ValidModel R) (h3 : lt_val valp n e.a3) (h6 : lt_val valp n e.a6) : lt_val valp n e.b6 :=
  by sorry

lemma lt_val_b8_of_a346 {p : R} (valp : NormalizedAddValuation p) (e : ValidModel R) (h3 : lt_val valp n e.a3) (h4 : lt_val valp n e.a4) (h6 : lt_val valp n e.a6) : lt_val valp n e.b8 :=
  by sorry

lemma lt_val_discr {p : R} (valp : NormalizedAddValuation p) (e : ValidModel R) (h4 : lt_val valp n e.b4) (h6 : lt_val valp n e.b6) (h8 : lt_val valp n e.b8) : lt_val valp n e.discr :=
  by sorry

def val_discr_to_nat {p : R} (valp : NormalizedAddValuation p) (e : ValidModel R) : ℕ := nat_of_val valp e.discr e.discr_not_zero

lemma iso_rst_val_discr_to_nat {p : R} (valp : NormalizedAddValuation p) (r s t : R) (e : ValidModel R) : val_discr_to_nat R valp (rst_iso r s t e) = val_discr_to_nat R valp e := by sorry

lemma ofN_val_discr_to_nat {p : R} (valp : NormalizedAddValuation p) (e : ValidModel R) : ofN (val_discr_to_nat R valp e) = valp.v e.discr := by
  delta val_discr_to_nat
  delta nat_of_val
  cases valp.v e.discr with
  | ofN n => simp
  | top => sorry

end ValidModel

open ValidModel

namespace Int

def center_mod (a b : ℤ) : ℤ :=
  let r := a % b; if 2 * r > b then r - b else if 2 * r <= -b then r + b else r

def dvr2 : DiscretelyValuedRing (2 : ℤ) := primeDVR prime_2
notation "nav2" => dvr2.valtn
notation "val2" => dvr2.valtn.v

lemma sub_val_mod_2 (x : ℤ) (n : ℕ) : (sub_val dvr2 x n) % 2 = if lt_val nav2 n x then 0 else sign x := by sorry

lemma val2_quadratic_disrc_not_zero (b c : ℤ) (H : ¬val2 (b * b + 4 * c) = 0) : ¬val2 b = 0 := by sorry

lemma val2_one : val2 1 = 0 := by rfl
lemma val2_mone : val2 (-1) = 0 := by rfl
lemma val2_sign (x : ℤ) : val2 (sign x) = 0 := by sorry


def decrease_val_2 (mval : ℕ) (e: ValidModel ℤ) : ValidModel ℤ × ℕ :=
  let n := e.val_discr_to_nat ℤ nav2;
  let xa3 := (sub_val dvr2 e.a3 mval) % 2;
  let xa6 := (sub_val dvr2 e.a6 (2 * mval)) % 2;
  if d1 : val2 (xa3 * xa3 + 4 * xa6) = 0 then
    (e, n - 2 * mval - 4)
  else
    have val_a3 : lt_val nav2 mval e.a3 := by sorry
    let e' := ValidModel.rst_iso 0 0 (2 ^ mval * xa6) e;
    let xa2' := (sub_val dvr2 e'.a2 1) % 2;
    let xa4' := (sub_val dvr2 e'.a4 (mval + 1)) % 2;
    let xa6' := (sub_val dvr2  e'.a6 (2* mval + 1)) % 2;
    if d2 : val2 (xa4' * xa4' - 4 * xa2' * xa6') = 0 then
      (e', n - 2 * mval - 5)
    else
      have val_a4' : lt_val nav2 mval e'.a4 := by sorry
      let r := 2 ^ mval * (center_mod (xa6' * xa2') 2);
      let e'' := ValidModel.rst_iso r 0 0 e';
      have val_a3'' : lt_val nav2 mval e''.a3 := by sorry
      have val_a4'' : lt_val nav2 mval e''.a4 := by sorry
      have val_a6'' : lt_val nav2 mval e''.a6 := by sorry
      have iso_iso_n : n = e''.val_discr_to_nat ℤ nav2 := by sorry
      have decreasing : n - (mval + 1) < n - mval := by
        apply Nat.sub_lt_sub_left
        . rw [lt_ofN, iso_iso_n, ofN_val_discr_to_nat]
          apply lt_val_discr
          . apply lt_val_b4
            . apply Or.inr (val_a3'')
            . exact val_a4''
          . apply lt_val_b6
            . exact val_a3''
            . exact val_a6''
          . apply lt_val_b8_of_a346
            . exact val_a3''
            . exact val_a4''
            . exact val_a6''
        . exact Nat.lt_succ_self mval;
      decrease_val_2 (mval + 1) e''
termination_by
  measure (fun ⟨m, e⟩ => e.val_discr_to_nat ℤ nav2 - m)
decreasing_by
  simp [measure, invImage, InvImage, Nat.lt_wfRel]
  rw [iso_rst_val_discr_to_nat, iso_rst_val_discr_to_nat]
  exact decreasing

def tate_big_prime {p : ℕ} (hp : nat_prime p) (e : ValidModel ℤ) : Kodaira × ℕ × ℕ × (ℤ × ℤ × ℤ × ℤ) :=
  let dvrp := primeDVR hp; let navp := dvrp.valtn; let valp := navp.v;
  let c4 := e.c4; let c6 := e.c6; let Δ := e.discr; let n := valp Δ;
  let ⟨vpj, k, integralInv⟩ := match valp (c4 ^ 3), n with
    | ∞, ofN v_Δ => (0, v_Δ, true)
    | ofN v_c4, ofN v_Δ => if v_c4 < v_Δ then ((v_c4 : ℤ) - (v_Δ : ℤ), v_c4, false) else (v_c4 - v_Δ, v_Δ, true)
    | _, ∞ => (0, 0, true); -- Valid models avoid this case
  let ⟨u, r, s, t⟩ :=
    if k < 12 then (1, 0, 0, 0) else
    let u' := p ^ (k / 12); let s' := if e.a1 % 2 = 1 then (u' - e.a1) / 2 else - e.a1 / 2; let a2' := e.a2 - s' * e.a1 - s' * s'; let r' := if a2' % 3 = 0 then - a2' / 3 else if a2' % 3 = 1 then (u' * u' - a2') / 3 else - (u' * u' + a2') / 3; let a3' := e.a3 + r' * e.a1; let t' := if a3' % 2 = 1 then (u' * u' * u' - a3')/2 else -a3' / 2; (u', r', s', t');
  let k := k % 12; let Δ := Δ / ofNat (u ^ 12); let c6 := c6 / ofNat (u ^ 6); let c4 := c4 / ofNat (u ^ 4);
  if not integralInv then
    let ν := natAbs vpj; match k with
    | 0 => (I ν, 1, if kronecker (-c6) p = 1 then ν else gcd 2 ν, (u, r, s, t))
    | 6 => (Is ν, 2, natAbs (3 + kronecker (if ν % 2 = 1 then (Δ * c6 / p ^ (ν + 9)) else (Δ / p ^ (ν + 6))) p), (u, r, s, t))
    | _ => (I 0, 0, 0, (0, 0, 0, 0))
  else
    match k with
    | 0 => (I 0,  0, 1, (u, r, s, t))
    | 2 => (II,   2, 1, (u, r, s, t))
    | 3 => (III,  2, 2, (u, r, s, t))
    | 4 => (IV,   2, natAbs (2 + kronecker (-6 * c6 / (p * p)) p), (u, r, s, t))
    | 6 => (Is 0, 2, 1 + 0, (u, r, s, t)) --nb of roots of a cubic
    | 8 => (IVs,  2, natAbs (2 + kronecker (-6 * c6 / (p ^ 4 : ℕ)) p), (u, r, s, t))
    | 9 => (IIIs, 2, 2, (u, r, s, t))
    | 10 => (IIs, 2, 1, (u, r, s, t))
    | _ => (I 0, 0, 0, (0, 0, 0, 0))



def tate_small_prime (p : ℕ) (e : ValidModel ℤ) : Kodaira × ℕ × ℤ × (ℤ × ℤ × ℤ × ℤ) :=
  let dvrp := primeDVR (if p = 2 then prime_2 else prime_3) ; let navp := dvrp.valtn; let valp := navp.v;
  let c4 := e.c4; let c6 := e.c6; let Δ := e.discr; let n := valp Δ;
  let ⟨vpj, k, integralInv⟩ := match valp (c4 ^ 3), n with
    | ∞, ofN v_Δ => (0, v_Δ, true)
    | ofN v_c4, ofN v_Δ => if v_c4 < v_Δ then ((v_c4 : ℤ) - (v_Δ : ℤ), v_c4, false) else (v_c4 - v_Δ, v_Δ, true)
    | _, ∞ => (0, 0, true); -- Valid models avoid this case
  let ⟨u, r, s, t⟩ :=
    if k < 12 then (1, 0, 0, 0) else
    let u' := p ^ (k / 12); let s' := if e.a1 % 2 = 1 then (u' - e.a1) / 2 else - e.a1 / 2; let a2' := e.a2 - s' * e.a1 - s' * s'; let r' := if a2' % 3 = 0 then - a2' / 3 else if a2' % 3 = 1 then (u' * u' - a2') / 3 else - (u' * u' + a2') / 3; let a3' := e.a3 + r' * e.a1; let t' := if a3' % 2 = 1 then (u' * u' * u' - a3')/2 else -a3' / 2; (u', r', s', t');
  let k := k % 12; let Δ := Δ / ofNat (u ^ 12); let c6 := c6 / ofNat (u ^ 6); let c4 := c4 / ofNat (u ^ 4);
  if not integralInv then
    let ν := natAbs vpj; match k with
    | 0 => (Kodaira.I ν, 1, if kronecker (-c6) p = 1 then ν else gcd 2 ν, (u, r, s, t))
    | 6 => (Kodaira.Is ν, 2, 3 + kronecker (if ν % 2 = 1 then (Δ * c6 / p ^ (ν + 9)) else (Δ / p ^ (ν + 6))) p, (u, r, s, t))
    | _ => (Kodaira.I 0, 0, 0, (0, 0, 0, 0))
  else
    match k with
    | 0 => (Kodaira.I 0,  0, 1, (u, r, s, t))
    | 2 => (Kodaira.II,   2, 1, (u, r, s, t))
    | 3 => (Kodaira.III,  2, 2, (u, r, s, t))
    | 4 => (Kodaira.IV,   2, 2 + kronecker (-6 * c6 / (p * p)) p, (u, r, s, t))
    | 6 => (Kodaira.Is 0, 2, 1 + 0, (u, r, s, t)) --nb of roots of a cubic
    | 8 => (Kodaira.IVs,  2, 2 + kronecker (-6 * c6 / (p*p*p*p)) p, (u, r, s, t))
    | 9 => (Kodaira.IIIs, 2, 2, (u, r, s, t))
    | 10 => (Kodaira.IIs, 2, 1, (u, r, s, t))
    | _ => (Kodaira.I 0, 0, 0, (0, 0, 0, 0))


end Int
