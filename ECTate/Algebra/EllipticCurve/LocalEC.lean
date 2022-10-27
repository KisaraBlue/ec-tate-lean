import ECTate.Algebra.EllipticCurve.Kronecker
import ECTate.Algebra.EllipticCurve.Model
import ECTate.Algebra.EllipticCurve.ValuedRing
import ECTate.Data.Nat.Enat
import Mathlib.Init.Data.Int.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Contrapose

open Enat

variable {R : Type u} [inst : IntegralDomain R]


namespace Model

variable {p : R}

def is_local_singular_point (valp : SurjVal p) (e : Model R) (P : R × R) : Prop :=
valp.v (weierstrass e P) > 0 ∧ valp.v (dweierstrass_dx e P) > 0 ∧ valp.v (dweierstrass_dy e P) > 0

lemma singular_of_val_discr (valp : SurjVal p) (e : Model R) (h : valp.v e.discr > 0) :
  ∃ P, is_local_singular_point valp e P :=
by
  sorry

def move_singular_point_to_origin_triple (evr : EnatValRing p) (e : Model R) : R × R × R :=
  match evr.residue_char with
  | 2 => (evr.norm_repr e.a4, 0, evr.norm_repr (e.a6 + e.a4 * e.a2))
  | 3 => (evr.norm_repr (-e.b6), 0, evr.norm_repr (e.a3 - e.b6 * e.a1))
  | _ => (0, 0, 0) --need to fill here

def move_singular_point_to_origin_iso (evr : EnatValRing p) (e : Model R) : Model R := rst_triple e (move_singular_point_to_origin_triple evr e)

lemma move_singular_point_to_origin (evr : EnatValRing p) (e : Model R) : (∃ P, is_local_singular_point valp e P) → is_local_singular_point valp (move_singular_point_to_origin_iso evr e) (0, 0) := by sorry

def pi_scaling (evr : EnatValRing p) (e : Model R) : Model R := {
  a1 := evr.sub_val e.a1 1,
  a2 := evr.sub_val e.a2 2,
  a3 := evr.sub_val e.a3 3,
  a4 := evr.sub_val e.a4 4,
  a6 := evr.sub_val e.a6 6
}

lemma pi_scaling_of_b2 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h2 : evr.valtn.v e.a2 ≥ ofN 2) :
  evr.sub_val e.b2 2 = evr.sub_val e.a1 1 * evr.sub_val e.a1 1 + 4 * evr.sub_val e.a2 2 := by
  rw [←evr.sub_val_mul_right h1, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val, ←evr.sub_val_mul_right h2, ←evr.sub_val_add _ _]
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn h1 h1
  . exact val_mul_ge_of_right_ge evr.valtn h2

lemma pi_scaling_of_b4 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4) : evr.sub_val e.b4 4 = evr.sub_val e.a1 1 * evr.sub_val e.a3 3 + 2 * evr.sub_val e.a4 4 := by
  rw [←evr.sub_val_mul_right h3, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val, ←evr.sub_val_mul_right h4, ←evr.sub_val_add _ _]
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn h1 h3
  . exact val_mul_ge_of_right_ge evr.valtn h4

lemma pi_scaling_of_b6 (evr : EnatValRing p) (e : Model R) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h6 : evr.valtn.v e.a6 ≥ ofN 6) : evr.sub_val e.b6 6 = evr.sub_val e.a3 3 * evr.sub_val e.a3 3 + 4 * evr.sub_val e.a6 6 := by
  rw [←evr.sub_val_mul_right h3, ←evr.sub_val_mul_left h3, evr.sub_val_sub_val, ←evr.sub_val_mul_right h6, ←evr.sub_val_add _ _]
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn h3 h3
  . exact val_mul_ge_of_right_ge evr.valtn h6

lemma pi_scaling_of_b8 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1)
  (h2 : evr.valtn.v e.a2 ≥ ofN 2) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4)
  (h6 : evr.valtn.v e.a6 ≥ ofN 6) :
  evr.sub_val e.b8 8 = evr.sub_val e.a1 1 * evr.sub_val e.a1 1 * evr.sub_val e.a6 6
    - evr.sub_val e.a1 1 * evr.sub_val e.a3 3 * evr.sub_val e.a4 4
    + 4 * evr.sub_val e.a2 2 * evr.sub_val e.a6 6
    + evr.sub_val e.a2 2 * evr.sub_val e.a3 3 * evr.sub_val e.a3 3
    - evr.sub_val e.a4 4 * evr.sub_val e.a4 4 :=
by
  rw [←evr.sub_val_mul_right h1, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val, ←evr.sub_val_mul_right h6, ←evr.sub_val_mul_left (val_mul_ge_of_both_ge evr.valtn h1 h1), evr.sub_val_sub_val]
  rw [←evr.sub_val_mul_right h3, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val, ←evr.sub_val_mul_right h4, ←evr.sub_val_mul_left (val_mul_ge_of_both_ge evr.valtn h1 h3), evr.sub_val_sub_val]
  rw [←evr.sub_val_mul_right h2, ←evr.sub_val_mul_right h6, ←evr.sub_val_mul_left (val_mul_ge_of_right_ge evr.valtn h2), evr.sub_val_sub_val]
  rw [←evr.sub_val_mul_left h2, ←evr.sub_val_mul_right h3, ←evr.sub_val_mul_right h3, evr.sub_val_sub_val, ←evr.sub_val_mul_left (val_mul_ge_of_both_ge evr.valtn h2 h3), evr.sub_val_sub_val]
  rw [←evr.sub_val_mul_right h4, ←evr.sub_val_mul_left h4, evr.sub_val_sub_val]
  have h116 := val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_both_ge evr.valtn h1 h1) h6
  have h134 := (val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_both_ge evr.valtn h1 h3) h4)
  have h26 := val_mul_ge_of_both_ge evr.valtn (@val_mul_ge_of_right_ge R _ (ofN 2) p evr.valtn 4 e.a2 h2) h6
  have h233 := val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_both_ge evr.valtn h2 h3) h3
  have h44 := val_mul_ge_of_both_ge evr.valtn h4 h4
  simp only [add_ofN] at h116
  rw [add_ofN, add_ofN, ←val_of_neg] at h134
  simp only [add_ofN] at h26
  simp only [add_ofN] at h233
  rw [add_ofN, ←val_of_neg] at h44

  rw [sub_eq_add_neg, sub_eq_add_neg, ←evr.sub_val_neg, ←evr.sub_val_neg, ←evr.sub_val_add h116 h134, ←evr.sub_val_add _ h26, ←evr.sub_val_add _ h233, ←evr.sub_val_add _ h44, ←sub_eq_add_neg, ←sub_eq_add_neg]
  . rfl
  . exact val_add_ge_of_ge evr.valtn (val_add_ge_of_ge evr.valtn (val_add_ge_of_ge evr.valtn h116 h134) h26) h233
  . exact val_add_ge_of_ge evr.valtn (val_add_ge_of_ge evr.valtn h116 h134) h26
  . exact val_add_ge_of_ge evr.valtn h116 h134

open EnatValRing in
lemma pi_scaling_of_discr (evr : EnatValRing p) (e : Model R)
  (hb2 : evr.valtn.v e.b2 ≥ ofN 2) (hb4 : evr.valtn.v e.b4 ≥ ofN 4)
  (hb6 : evr.valtn.v e.b6 ≥ ofN 6) (hb8 : evr.valtn.v e.b8 ≥ ofN 8) :
  evr.sub_val e.discr 12 = -evr.sub_val e.b2 2 * evr.sub_val e.b2 2 * evr.sub_val e.b8 8
    - 8 * ((evr.sub_val e.b4 4) ^ 3) - 27 * evr.sub_val e.b6 6 * evr.sub_val e.b6 6
    + 9 * evr.sub_val e.b2 2 * evr.sub_val e.b4 4 * evr.sub_val e.b6 6 :=
by
  rw [discr,
      sub_val_add,
      sub_val_sub,
      sub_val_sub,
      sub_val_mul _ 4 8 _ _ hb8,
      sub_val_mul _ 2 2 _ _ hb2,
      sub_val_mul _ 6 6 _ _ hb6,
      sub_val_mul_right _ hb6,
      sub_val_mul _ 6 6 _ _ hb6,
      sub_val_mul _ 2 4 _ _ hb4,
      sub_val_mul_right _ hb2,
      sub_val_mul_right,
      sub_val_pow _ _ _ _ hb4,
      sub_val_neg]
  . rfl
  . sorry
  . norm_num
  . sorry
  . norm_num
  . sorry
  . norm_num
  . sorry
  . norm_num
  . sorry
  . norm_num
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry

lemma b2_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h2 : evr.valtn.v e.a2 ≥ ofN 2) : (pi_scaling evr e).b2 = evr.sub_val e.b2 2 := by
  simp only [b2, pi_scaling]
  exact (pi_scaling_of_b2 evr e h1 h2).symm

lemma b4_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4) : (pi_scaling evr e).b4 = evr.sub_val e.b4 4 := by
  simp only [b4, pi_scaling]
  exact (pi_scaling_of_b4 evr e h1 h3 h4).symm

lemma b6_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h6 : evr.valtn.v e.a6 ≥ ofN 6) : (pi_scaling evr e).b6 = evr.sub_val e.b6 6 := by
  simp only [b6, pi_scaling]
  exact (pi_scaling_of_b6 evr e h3 h6).symm

lemma b8_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h2 : evr.valtn.v e.a2 ≥ ofN 2) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4) (h6 : evr.valtn.v e.a6 ≥ ofN 6) : (pi_scaling evr e).b8 = evr.sub_val e.b8 8 := by
  simp only [b8, pi_scaling]
  exact (pi_scaling_of_b8 evr e h1 h2 h3 h4 h6).symm

lemma val_b2_of_val_a12 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h2 : evr.valtn.v e.a2 ≥ ofN 2) : evr.valtn.v e.b2 ≥ ofN 2 := by
  simp only [b2]
  apply val_add_ge_of_ge
  . apply val_mul_ge_of_both_ge evr.valtn h1 h1
  . apply val_mul_ge_of_right_ge evr.valtn h2

lemma val_b4_of_val_a134 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4) : evr.valtn.v e.b4 ≥ ofN 4 := by
  simp only [b4]
  apply val_add_ge_of_ge
  . apply val_mul_ge_of_both_ge evr.valtn h1 h3
  . apply val_mul_ge_of_right_ge evr.valtn h4

lemma val_b6_of_val_a36 (evr : EnatValRing p) (e : Model R) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h6 : evr.valtn.v e.a6 ≥ ofN 6) : evr.valtn.v e.b6 ≥ ofN 6 := by
  simp only [b6]
  apply val_add_ge_of_ge
  . apply val_mul_ge_of_both_ge evr.valtn h3 h3
  . apply val_mul_ge_of_right_ge evr.valtn h6

lemma val_b8_of_val_ai (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h2 : evr.valtn.v e.a2 ≥ ofN 2) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4) (h6 : evr.valtn.v e.a6 ≥ ofN 6) : evr.valtn.v e.b8 ≥ ofN 8 := by
  simp only [b8, sub_eq_add_neg]
  apply val_add_ge_of_ge
  . apply val_add_ge_of_ge
    . apply val_add_ge_of_ge
      . apply val_add_ge_of_ge
        . apply val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ h1 h1) h6
        . rw [val_of_neg]
          apply val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ h1 h3) h4
      . rw [mul_assoc]
        apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ h2 h6)
    . apply val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ h2 h3) h3
  . rw [val_of_neg]
    apply val_mul_ge_of_both_ge _ h4 h4

lemma discr_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h2 : evr.valtn.v e.a2 ≥ ofN 2) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4) (h6 : evr.valtn.v e.a6 ≥ ofN 6) : (pi_scaling evr e).discr = evr.sub_val e.discr 12 := by
  simp only [discr, b2_of_pi_scaling evr e h1 h2, b4_of_pi_scaling evr e h1 h3 h4, b6_of_pi_scaling evr e h3 h6, b8_of_pi_scaling evr e h1 h2 h3 h4 h6]
  exact (pi_scaling_of_discr evr e (val_b2_of_val_a12 evr e h1 h2) (val_b4_of_val_a134 evr e h1 h3 h4) (val_b6_of_val_a36 evr e h3 h6) (val_b8_of_val_ai evr e h1 h2 h3 h4 h6)).symm

lemma val_discr_of_val_ai (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h2 : evr.valtn.v e.a2 ≥ ofN 2) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4) (h6 : evr.valtn.v e.a6 ≥ ofN 6) : evr.valtn.v e.discr ≥ ofN 12 := by
  have hb2 := val_b2_of_val_a12 evr e h1 h2
  have hb4 := val_b4_of_val_a134 evr e h1 h3 h4
  have hb6 := val_b6_of_val_a36 evr e h3 h6
  have hb8 := val_b8_of_val_ai evr e h1 h2 h3 h4 h6
  simp only [discr, sub_eq_add_neg]
  apply val_add_ge_of_ge
  . apply val_add_ge_of_ge
    . apply val_add_ge_of_ge
      . rw [←neg_mul_left, ←neg_mul_left, val_of_neg]
          apply val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ hb2 hb2) hb8
      . rw [val_of_neg, pow_succ', pow_succ', pow_one]
        apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ hb4 hb4) hb4)
    . rw [val_of_neg, mul_assoc]
      apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ hb6 hb6)
  . rw [mul_assoc, mul_assoc]
    apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ hb2 (val_mul_ge_of_both_ge _ hb4 hb6))

end Model


namespace ValidModel

def pi_scaling (evr : EnatValRing p) (e : ValidModel R) (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h2 : evr.valtn.v e.a2 ≥ ofN 2) (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4) (h6 : evr.valtn.v e.a6 ≥ ofN 6) : ValidModel R := {
  toModel := Model.pi_scaling evr (e.toModel),
  discr_not_zero := by
    rw [Model.discr_of_pi_scaling evr e.toModel h1 h2 h3 h4 h6]
    intro H
    have H' := let_value_eq (fun (x:R) => p ^ 12 * x) H
    simp only [mul_zero] at H'
    rw [←evr.factor_p_of_le_val (Model.val_discr_of_val_ai evr e.toModel h1 h2 h3 h4 h6)] at H'
    apply e.discr_not_zero H'
}

def val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) : ℕ := nat_of_val valp e.discr_not_zero

@[simp]
lemma iso_rst_val_discr_to_nat {p : R} (valp : SurjVal p) (r s t : R) (e : ValidModel R) :
  val_discr_to_nat valp (rst_iso r s t e) = val_discr_to_nat valp e :=
by simp [val_discr_to_nat, nat_of_val, ValidModel.rst_iso, Model.rst_discr]

lemma pi_scaling_val_discr_to_nat {p : R} (evr : EnatValRing p) (e : ValidModel R)
  (h1 : evr.valtn.v e.a1 ≥ ofN 1) (h2 : evr.valtn.v e.a2 ≥ ofN 2)
  (h3 : evr.valtn.v e.a3 ≥ ofN 3) (h4 : evr.valtn.v e.a4 ≥ ofN 4) (h6 : evr.valtn.v e.a6 ≥ ofN 6) :
  val_discr_to_nat evr.valtn (pi_scaling evr e h1 h2 h3 h4 h6) = val_discr_to_nat evr.valtn e - 12 :=
by sorry

lemma ofN_val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) : ofN (val_discr_to_nat valp e) = valp.v e.discr := by
  cases h : valp.v e.discr with
  | ofN n =>
    rw [val_discr_to_nat, nat_of_val, ofN_to_nat_eq_self]
    assumption
  | top =>
    exfalso
    rw [valp.v_eq_top_iff_zero] at h
    exact e.discr_not_zero h

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
  simp only [Model.b8]
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
  simp only [Model.discr]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply val_add_ge_of_ge valp
  . apply val_add_ge_of_ge valp
    . apply val_add_ge_of_ge valp
      . rw [←neg_mul_left, ←neg_mul_left, val_of_neg, (show 3 = 1 + 1 + 1 by rfl), ←Nat.add_assoc, ←Nat.add_assoc, Nat.add_assoc, mul_comm, ←add_ofN]
        exact val_mul_ge_of_both_ge valp h8' (val_mul_ge_of_both_ge valp h2' h2')
      . rw [val_of_neg, pow_succ', pow_succ', pow_one, ←add_self_eq_mul_two, (show q + q + 3 = q + 1 + (q + 1) + 1 by ring), ←add_ofN, ←add_ofN]
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
  simp only [rst_iso]
  rw [Model.rst_b2]
  apply val_add_ge_of_ge valp h_b2
  exact val_mul_ge_of_left_ge valp h_p

section cubic

def Δcubic (c : R × R × R) : R := 18 * c.1 * c.2.1 * c.2.2 - 4 * c.1 ^ 3 * c.2.2 + c.1 ^ 2 * c.2.1 ^ 2 - 4 * c.2.1 ^ 3 - 27 * c.2.2 ^ 2

def model_to_cubic {p : R} (evr : EnatValRing p) (e : ValidModel R) : R × R × R := (evr.sub_val e.a2 1, evr.sub_val e.a4 2, evr.sub_val e.a6 3)

def cubic_has_dinstinct_roots {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop := evr.valtn.v (Δcubic (model_to_cubic evr e)) = 0

def δmultiplicity (c : R × R × R) : R := 3 * c.2.1 - c.1 ^ 2

def cubic_has_double_root {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop := evr.valtn.v (Δcubic (model_to_cubic evr e)) > 0 ∧ evr.valtn.v (δmultiplicity (model_to_cubic evr e)) = 0

def cubic_has_triple_root {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop := evr.valtn.v (Δcubic (model_to_cubic evr e)) > 0 ∧ evr.valtn.v (δmultiplicity (model_to_cubic evr e)) > 0

def move_cubic_double_root_to_origin_iso {p : R} (evr : EnatValRing p) (e : ValidModel R) : ValidModel R :=
  let (a2p, a4p2, a6p3) := model_to_cubic evr e
  rst_iso (p * (evr.norm_repr (if evr.residue_char = 2 then a4p2 else a2p * a4p2))) 0 0 e

def cubic_double_root_is_zero {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
  let (a2p, a4p2, a6p3) := model_to_cubic evr e
  evr.valtn.v a2p = 0 ∧ evr.valtn.v a4p2 > 0 ∧ evr.valtn.v a6p3 > 0

lemma move_cubic_double_root_to_origin {p : R} (evr : EnatValRing p) (e : ValidModel R) : cubic_has_double_root evr e → cubic_double_root_is_zero evr (move_cubic_double_root_to_origin_iso evr e) := sorry

def move_cubic_triple_root_to_origin_iso {p : R} (evr : EnatValRing p) (e : ValidModel R) : ValidModel R :=
  let (a2p, a4p2, a6p3) := model_to_cubic evr e
  rst_iso (p * (evr.norm_repr (if evr.residue_char = 2 then -a2p else -a6p3))) 0 0 e

def cubic_triple_root_is_zero {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
  let (a2p, a4p2, a6p3) := model_to_cubic evr e
  evr.valtn.v a2p > 0 ∧ evr.valtn.v a4p2 > 0 ∧ evr.valtn.v a6p3 > 0

lemma move_cubic_triple_root_to_origin {p : R} (evr : EnatValRing p) (e : ValidModel R) : cubic_has_triple_root evr e → cubic_triple_root_is_zero evr (move_cubic_triple_root_to_origin_iso evr e) := sorry

end cubic


end ValidModel
