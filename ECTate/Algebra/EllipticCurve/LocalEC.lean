import Mathlib.Algebra.EllipticCurve.Kronecker
import Mathlib.Algebra.EllipticCurve.Model
import Mathlib.Algebra.EllipticCurve.ValuedRing
import Mathlib.Data.Nat.Enat
import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.Data.Int.Order
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NormNum

open Enat

namespace Model

variable {R : Type u}
variable {p : R}

section

variable [IntegralDomain R]

def local_singular_point (valp : SurjVal p) (e : Model R) (P : R × R) : Prop := valp.v (weierstrass e P) > 0 ∧ valp.v (dweierstrass_dx e P) > 0 ∧ valp.v (dweierstrass_dy e P) > 0

lemma singular_of_val_discr (valp : SurjVal p) (e : Model R) : valp.v e.discr > 0 → ∃ P, local_singular_point valp e P := by sorry

end

variable [evrp : EnatValRing p]

def move_singular_point_to_origin_triple (e : Model R) : R × R × R :=
  match evrp.residue_char with
  | 2 => (evrp.norm_repr p e.a4, 0, evrp.norm_repr p (e.a6 + e.a4 * e.a2))
  | 3 => (evrp.norm_repr p (-e.b6), 0, evrp.norm_repr p (e.a3 - e.b6 * e.a1))
  | c => (0, 0, 0) --need to fill here

def move_singular_point_to_origin_iso (e : Model R) : Model R := rst_triple e (move_singular_point_to_origin_triple e)

lemma move_singular_point_to_origin (e : Model R) : (∃ P, local_singular_point evrp.valtn e P) → local_singular_point valp (move_singular_point_to_origin_iso e) (0, 0) := by sorry


end Model

variable {R : Type u} [IntegralDomain R]

namespace ValidModel

def val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) : ℕ := nat_of_val valp e.discr_not_zero

@[simp]lemma iso_rst_val_discr_to_nat {p : R} (valp : SurjVal p) (r s t : R) (e : ValidModel R) : val_discr_to_nat valp (rst_iso r s t e) = val_discr_to_nat valp e := by sorry

lemma ofN_val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) : ofN (val_discr_to_nat valp e) = valp.v e.discr := by
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
  have h2' := v_b2_of_v_a1_a2 valp e h1 h2
  have h4' := v_b4_of_v_a1_a3_a4 valp e h1 h3 h4
  have h6' := v_b6_of_v_a3_a6 valp e h3 h6
  have h8' := v_b8_of_v_ai valp e h1 h2 h3 h4 h6
  simp [Model.discr]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply val_add_ge_of_ge valp
  . apply val_add_ge_of_ge valp
    . apply val_add_ge_of_ge valp
      . rw [←neg_mul_left, ←neg_mul_left, val_of_neg, (show 3 = 1 + 1 + 1 by rfl), ←Nat.add_assoc, ←Nat.add_assoc, Nat.add_assoc, mul_comm, ←add_ofN]
        exact val_mul_ge_of_both_ge valp h8' (val_mul_ge_of_both_ge valp h2' h2')
      . rw [val_of_neg, pow_succ, pow_succ, pow_one, ←add_self_eq_mul_two, (show q + q + 3 = q + 1 + (q + 1) + 1 by ring), ←add_ofN, ←add_ofN]
        exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp (val_mul_ge_of_both_ge valp h4' h4') (Enat.le_trans ((le_ofN _ _).1 (Nat.le_add_left 1 q)) h4'))
    . rw [val_of_neg, ←add_ofN, mul_assoc, (show 3 = 2 + 1 by rfl)]
      apply val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h6' (Enat.le_trans ((le_ofN _ _).1 _) h6'))
      rw [←add_self_eq_mul_two q]
      exact Nat.add_le_add (Nat.succ_le_of_lt hq) (Nat.le_of_lt hq)
  . rw [(show 3 = 1 + (1 + 1) by rfl), ←add_ofN, ←add_ofN, mul_comm, mul_assoc 9]
    exact val_mul_ge_of_both_ge valp h6' (val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h2' (Enat.le_trans ((le_ofN _ _).1 (Nat.add_le_add (Nat.le_of_lt hq) (le_of_eq rfl))) h4')))

lemma small_char_div_12 {p : R} (hp : p = 2 ∨ p = 3) (valp : SurjVal p) : valp.v 12 ≥ ofN 1 := by
  cases hp with
  | inl p2 =>
    rw [(show (12 : R) = 2 * 6 by norm_num)]
    apply val_mul_ge_of_left_ge
    rw [←p2]
    exact le_of_eq (valp.v_uniformizer).symm
  | inr p3 =>
    rw [(show (12 : R) = 3 * 4 by norm_num)]
    apply val_mul_ge_of_left_ge
    rw [←p3]
    exact le_of_eq (valp.v_uniformizer).symm


lemma v_rst_b2_of_small_char {p : R} (valp : SurjVal p) (e : ValidModel R) (r s t : R) (h_b2 : valp.v e.b2 ≥ ofN 1) (h_p : valp.v 12 ≥ ofN 1) : valp.v (rst_iso r s t e).b2 ≥ ofN 1 := by
  simp [rst_iso]
  rw [Model.rst_b2]
  apply val_add_ge_of_ge valp h_b2
  exact val_mul_ge_of_left_ge valp h_p

section cubic

def Δcubic (b c d : R) : R := 18 * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * c ^ 3 - 27 * d ^ 2

--def model_to_cubic

def cubic_has_dinstinct_roots {p : R} (valp : SurjVal p) (b c d : R) : Prop := valp.v (Δcubic b c d) = 0

def δmultiplicity (b c d : R) : R := 3 * c - b ^ 2

def cubic_has_double_root {p : R} (valp : SurjVal p) (b c d : R) : Prop := valp.v (Δcubic b c d) > 0 ∧ valp.v (δmultiplicity b c d) = 0

def cubic_has_triple_root {p : R} (valp : SurjVal p) (b c d : R) : Prop := valp.v (Δcubic b c d) > 0 ∧ valp.v (δmultiplicity b c d) > 0

--def move_cubic_double_root_to_origin_iso {p : R} (evrp : EnatValRing p) (e : Model R) : Model R := rst_iso (p * (evrp.norm_repr p (if evrp.residue_char = 2 then a4p2 else a2p * a4p2))) 0 0 e

end cubic


end ValidModel
