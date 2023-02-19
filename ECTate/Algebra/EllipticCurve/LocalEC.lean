import ECTate.Algebra.EllipticCurve.Kronecker
import ECTate.Algebra.EllipticCurve.Model
import ECTate.Algebra.ValuedRing
import ECTate.Data.Nat.Enat
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Contrapose

open Enat

variable {R : Type u} [inst : IntegralDomain R]


namespace Model

variable {p : R}

def is_local_singular_point (evr : EnatValRing p) (e : Model R) (P : R × R) : Prop :=
evr.residue.repr_p (weierstrass e P) = ⟦0⟧ ∧ evr.residue.repr_p (dweierstrass_dx e P) = ⟦0⟧ ∧ evr.residue.repr_p (dweierstrass_dy e P) = ⟦0⟧

lemma singular_of_val_discr (evr : EnatValRing p) (e : Model R) (h : Quotient.mk (val_setoid evr.valtn) e.discr = ⟦0⟧) :
  ∃ P, is_local_singular_point evr e P := by
  sorry

lemma val_discr_of_singular (evr : EnatValRing p) (e : Model R) (h : ∃ P, is_local_singular_point evr e P) : Quotient.mk (val_setoid evr.valtn) e.discr = ⟦0⟧ := by
  sorry

def move_singular_point_to_origin_triple (evr : EnatValRing p) (e : Model R) : R × R × R :=
  match evr.residue.char with
  | 2 => ((evr.lift e.a4), 0, evr.lift (e.a6 + e.a4 * e.a2))
  | 3 => (evr.lift (-e.b6), 0, evr.lift (e.a3 - e.b6 * e.a1))
  | _ => (0, 0, 0) --need to fill here
/-evr.residue.lift_def-/


def move_singular_point_to_origin_iso (evr : EnatValRing p) (e : Model R) : Model R :=
rst_triple e (move_singular_point_to_origin_triple evr e)

section char2

lemma ring_two_is_char (evr : EnatValRing p) (hc : evr.residue.char = 2) : 2 = (evr.residue.char : R) := by rw [hc]; rfl

lemma neg_quot_char2 (evr : EnatValRing p) (hc : evr.residue.char = 2) (x : R) :  -Quotient.mk (val_setoid evr.valtn) x = ⟦x⟧ := by
  rw [neg_quot_eq_quot_neg, (show -x = x + 2 * -x by ring), add_quot_eq_quot_add, ring_two_is_char evr hc, evr.residue.quot_char_mul, ←quot_zero, add_zero]


lemma b2_equiv_a1_of_char2 (evr : EnatValRing p) (hc : evr.residue.char = 2) (e : Model R) : Quotient.mk (val_setoid evr.valtn) e.b2 = ⟦e.a1⟧ := by
  rw [b2, add_quot_eq_quot_add, (show 4 = 2 * 2 by norm_num), mul_assoc]
  have h := evr.residue.quot_char_mul (2 * e.a2)
  rw [hc, (show ((2 : ℕ) : R) = 2 by rfl)] at h
  rw [h, ←pow_two, ←hc, evr.residue.quot_pow_char, ←add_quot_eq_quot_add, add_zero]

lemma discr_equiv_a3_of_char2 (evr : EnatValRing p) (hc : evr.residue.char = 2) (e : Model R) (hb2 : evr.valtn.v e.b2 > 0) : Quotient.mk (val_setoid evr.valtn) e.discr = ⟦e.a3⟧ := by
  rw [discr, sub_eq_add_neg, sub_eq_add_neg, add_quot_eq_quot_add,  add_quot_eq_quot_add,  add_quot_eq_quot_add,  mul_comm _ e.b2, mul_assoc, quot_pos_val_mul hb2, (show -(8 * b4 e ^ 3) = 2 * (-4 * e.b4 ^ 3) by ring)]
  rw [mul_comm 9, mul_assoc e.b2, mul_assoc e.b2, quot_pos_val_mul hb2, (show -(27 * b6 e * b6 e) = b6 e * b6 e + 2 * (-14 * b6 e * b6 e) by ring), add_quot_eq_quot_add, ring_two_is_char evr hc, quot_pos_val_mul evr.residue.val_char, quot_pos_val_mul evr.residue.val_char, ←pow_two, ←hc, evr.residue.quot_pow_char, b6, add_quot_eq_quot_add, (show 4 * e.a6 = 2 * (2 * e.a6) by ring), ring_two_is_char evr hc, quot_pos_val_mul evr.residue.val_char, ←quot_zero, zero_add, zero_add, add_zero, add_zero, add_zero, ←pow_two, ←hc, evr.residue.quot_pow_char]


lemma move_singular_point_to_origin_char2 (evr : EnatValRing p) (e : Model R) (hc : evr.residue.char = 2) (hb2 : evr.valtn.v e.b2 > 0) :
(∃ P, is_local_singular_point evr e P) →
  is_local_singular_point evr (move_singular_point_to_origin_iso evr e) (0, 0) := by
    intro h_sing
    simp [is_local_singular_point, ResidueRing.repr_p, move_singular_point_to_origin_iso, move_singular_point_to_origin_triple, rst_triple, hc, rst_iso]
    apply And.intro
    . simp [weierstrass,sub_eq_add_neg, add_quot_eq_quot_add, mul_quot_eq_quot_mul, evr.quot_lift, ←neg_quot_eq_quot_neg]
      rw [←b2_equiv_a1_of_char2 evr hc e, ←discr_equiv_a3_of_char2 evr hc e hb2, val_discr_of_singular evr e h_sing, quot_pos_val hb2, ←quot_zero, zero_add, mul_zero, add_zero,←pow_two, ←mul_quot_eq_quot_mul, ←add_quot_eq_quot_add, quot_pow_eq_quot_of_pow]
      simp [←@mul_quot_eq_quot_mul _ _ _ _ _ e.a4, ←pow_two e.a4, ←hc, evr.residue.quot_pow_char]
      rw [←mul_quot_eq_quot_mul, add_quot_eq_quot_add]
      conv in -Quotient.mk (val_setoid evr.valtn) e.a4 + -Quotient.mk (val_setoid evr.valtn) e.a6 => rw [neg_quot_char2 evr hc]
      rw [add_comm (-⟦e.a4⟧), add_comm (⟦e.a4⟧), add_assoc _ _ (-⟦e.a4⟧), add_assoc _ _ (-⟦e.a4⟧), add_neg_self, add_zero, ←neg_add, ←add_quot_eq_quot_add, ←add_quot_eq_quot_add, add_comm e.a6, add_neg_self]
    apply And.intro
    . simp [dweierstrass_dx,sub_eq_add_neg, add_quot_eq_quot_add, mul_quot_eq_quot_mul, evr.quot_lift, ←neg_quot_eq_quot_neg]
      rw [←b2_equiv_a1_of_char2 evr hc e, quot_pos_val hb2, ring_two_is_char evr hc, evr.residue.quot_char, ←quot_zero]
      simp
      rw [mul_assoc, ←mul_quot_eq_quot_mul, ←pow_two, ←hc, evr.residue.quot_pow_char, ←neg_add, ←mul_quot_eq_quot_mul, ←add_quot_eq_quot_add, (show 3 * e.a4 + e.a4 = 2 * (2 * e.a4) by ring), ring_two_is_char evr hc, evr.residue.quot_char_mul, ←quot_zero, neg_zero]
    . simp [dweierstrass_dy,sub_eq_add_neg, add_quot_eq_quot_add, mul_quot_eq_quot_mul, evr.quot_lift, ←neg_quot_eq_quot_neg]
      rw [←b2_equiv_a1_of_char2 evr hc e, ←discr_equiv_a3_of_char2 evr hc e hb2, val_discr_of_singular evr e h_sing, quot_pos_val hb2, ring_two_is_char evr hc, evr.residue.quot_char, ←quot_zero]
      simp

end char2

section char3

lemma ring_three_is_char (evr : EnatValRing p) (hc : evr.residue.char = 3) : 3 = (evr.residue.char : R) := by rw [hc]; rfl

lemma neg_eq_two_mul (evr : EnatValRing p) (hc : evr.residue.char = 3) (x : R) : Quotient.mk (val_setoid evr.valtn) (-x) = ⟦2 * x⟧ := by
  rw [(show -x = 2 * x + 3 * -x by ring), add_quot_eq_quot_add, (show 3 = ((3 : ℕ) : R) by rfl), ←hc, evr.residue.quot_char_mul, ←quot_zero, add_zero]

lemma b2_equiv_of_char3 (evr : EnatValRing p) (hc : evr.residue.char = 3) (e : Model R) : Quotient.mk (val_setoid evr.valtn) e.b2 = ⟦e.a1 * e.a1 + e.a2⟧ := by
  rw [b2, add_quot_eq_quot_add, (show 4 = 3 + 1 by norm_num), add_mul]
  have h := evr.residue.quot_char_mul e.a2
  rw [hc, (show ((3 : ℕ) : R) = 3 by rfl)] at h
  rw [add_quot_eq_quot_add, h, one_mul, ←quot_zero, zero_add, ←add_quot_eq_quot_add]

lemma discr_equiv_of_char3 (evr : EnatValRing p) (hc : evr.residue.char = 3) (e : Model R) (hb2 : evr.valtn.v e.b2 > 0) : Quotient.mk (val_setoid evr.valtn) e.discr = ⟦e.a1 * e.a3 + 2 * e.a4⟧ := by
  rw [discr, sub_eq_add_neg, sub_eq_add_neg, add_quot_eq_quot_add,  add_quot_eq_quot_add,  add_quot_eq_quot_add,  mul_comm _ e.b2, mul_assoc, quot_pos_val_mul hb2, (show -(8 * b4 e ^ 3) = b4 e ^ 3 + 3 * (-3 * b4 e ^ 3) by ring), (show -(27 * b6 e * b6 e) = 3 * (-9 * b6 e ^ 2) by ring), (show 9 * b2 e * b4 e * b6 e = 3 * (3 * b2 e * b4 e * b6 e) by ring), ring_three_is_char evr hc, evr.residue.quot_char_mul, evr.residue.quot_char_mul, add_quot_eq_quot_add, evr.residue.quot_char_mul, ←quot_zero]
  simp
  rw [←hc, evr.residue.quot_pow_char, b4]


lemma move_singular_point_to_origin_char3 (evr : EnatValRing p) (e : Model R) (hc : evr.residue.char = 3) (hb2 : evr.valtn.v e.b2 > 0) :
(∃ P, is_local_singular_point evr e P) →
  is_local_singular_point evr (move_singular_point_to_origin_iso evr e) (0, 0) := by
    intro h_sing
    simp [is_local_singular_point, ResidueRing.repr_p, move_singular_point_to_origin_iso, move_singular_point_to_origin_triple, rst_triple, hc, rst_iso]
    apply And.intro
    . simp [weierstrass,sub_eq_add_neg, add_quot_eq_quot_add, mul_quot_eq_quot_mul, evr.quot_lift, ←neg_quot_eq_quot_neg]
      simp [neg_quot_eq_quot_neg, ←add_quot_eq_quot_add, ←mul_quot_eq_quot_mul]
      rw [(show -(b6 e * b6 e * e.a2) + (b6 e * e.a4 + -e.a6) = -b6 e * -b6 e * -e.a2 + (-b6 e * -e.a4 + -e.a6) by ring), neg_mul_left]
      rw [(show (e.a3 + -b6 e * e.a1) * (e.a3 + (e.a3 + -b6 e * e.a1) + -b6 e * e.a1) + (b6 e * b6 e * b6 e + (-b6 e * -b6 e * -e.a2 + (-b6 e * -e.a4 + -e.a6))) = (-e.b6 * -e.b6) * (2 * (e.a1 * e.a1) + -e.a2) + (2 * (e.a3 * e.a3) + -e.a6) + -e.b6 * (4 * e.a1 * e.a3 + -e.a4) + e.b6 ^ 3 by ring)]
      simp [add_quot_eq_quot_add]
      rw [mul_quot_eq_quot_mul]
      conv in Quotient.mk (val_setoid evr.valtn) (2 * (e.a1 * e.a1) + -e.a2) => rw [add_quot_eq_quot_add, ←neg_eq_two_mul evr hc, ←neg_quot_eq_quot_neg, ←neg_quot_eq_quot_neg, ←neg_add, ←add_quot_eq_quot_add, ←b2_equiv_of_char3 evr hc, quot_pos_val hb2]
      conv in Quotient.mk (val_setoid evr.valtn) (2 * (e.a3 * e.a3)) + Quotient.mk (val_setoid evr.valtn) (-e.a6) => rw [←neg_eq_two_mul evr hc, ←neg_neg e.a6, neg_eq_two_mul evr hc (- -e.a6), ←neg_mul_right, neg_eq_two_mul evr hc (2 * _), ←neg_mul_right, ←neg_mul_right, ←add_quot_eq_quot_add, ←neg_add, (show 2 * (2 * e.a6) = 4 * e.a6 by ring), ←neg_quot_eq_quot_neg, ←b6]
      conv in Quotient.mk (val_setoid evr.valtn) (-(b6 e * (4 * e.a1 * e.a3 + -e.a4))) => rw [←neg_quot_eq_quot_neg, mul_quot_eq_quot_mul, add_quot_eq_quot_add, neg_eq_two_mul evr hc, (show 4 * e.a1 * e.a3 = 2 * (2 *( e.a1 * e.a3)) by ring), ←neg_eq_two_mul evr hc, neg_mul_right 2, ←neg_eq_two_mul evr hc, neg_neg, ←add_quot_eq_quot_add, ←discr_equiv_of_char3 evr hc e hb2, val_discr_of_singular evr e h_sing]
      rw [←hc, evr.residue.quot_pow_char, ←quot_zero]
      simp
    apply And.intro
    . simp [dweierstrass_dx,sub_eq_add_neg, add_quot_eq_quot_add, mul_quot_eq_quot_mul, evr.quot_lift, ←neg_quot_eq_quot_neg]
      rw [(show 3 = ((3 : ℕ) : R) by rfl), ←hc, evr.residue.quot_char, ←quot_zero]
      simp [neg_quot_eq_quot_neg, ←add_quot_eq_quot_add, ←mul_quot_eq_quot_mul]
      rw [(show (e.a3 + -(b6 e * e.a1)) * e.a1 + (2 * b6 e * e.a2 + -e.a4) = e.b6 * (-(e.a1 * e.a1) + 2 * e.a2) + (e.a1 * e.a3 + -e.a4) by ring)]
      simp [add_quot_eq_quot_add]
      conv in Quotient.mk (val_setoid evr.valtn) (b6 e * (-(e.a1 * e.a1) + 2 * e.a2)) => rw [mul_quot_eq_quot_mul, add_quot_eq_quot_add, ←neg_quot_eq_quot_neg, ←neg_eq_two_mul evr hc, ←neg_quot_eq_quot_neg, ←neg_add, ←add_quot_eq_quot_add, ←b2_equiv_of_char3 evr hc, quot_pos_val hb2]
      rw [neg_eq_two_mul evr hc, ←add_quot_eq_quot_add, ←discr_equiv_of_char3 evr hc e hb2, val_discr_of_singular evr e h_sing, ←quot_zero]
      simp
    . simp [dweierstrass_dy,sub_eq_add_neg, add_quot_eq_quot_add, mul_quot_eq_quot_mul, evr.quot_lift, ←neg_quot_eq_quot_neg]
      simp [neg_quot_eq_quot_neg, ←add_quot_eq_quot_add, ←mul_quot_eq_quot_mul]
      rw [←one_mul (e.a3 + -(b6 e * e.a1)), ←mul_assoc, mul_one, ←add_mul, (show 1+2 = ((3:ℕ):R) by norm_num), ←hc, evr.residue.quot_char_mul]



end char3

lemma move_singular_point_to_origin_bigchar (evr : EnatValRing p) (e : Model R) (hc : evr.residue.char ≠ 2 ∧ evr.residue.char ≠ 3) :
(∃ P, is_local_singular_point evr e P) →
  is_local_singular_point evr (move_singular_point_to_origin_iso evr e) (0, 0) := by
    intro h_sing
    --simp [is_local_singular_point, ResidueRing.repr_p, move_singular_point_to_origin_iso, move_singular_point_to_origin_triple, rst_triple, hc, rst_iso]
    sorry

lemma characteristic_disj (evr : EnatValRing p) : evr.residue.char = 2 ∨ evr.residue.char = 3 ∨ (evr.residue.char ≠ 2 ∧ evr.residue.char ≠ 3) := by
  cases em (evr.residue.char = 2) with
  | inl h => exact Or.intro_left _ h
  | inr h => cases em (evr.residue.char = 3) with
    | inl h' => exact Or.intro_right _ (Or.intro_left _ h')
    | inr h' => exact Or.intro_right _ (Or.intro_right _ (And.intro h h'))

lemma move_singular_point_to_origin (evr : EnatValRing p) (e : Model R) (hb2 : evr.valtn.v e.b2 > 0) :
(∃ P, is_local_singular_point evr e P) →
  is_local_singular_point evr (move_singular_point_to_origin_iso evr e) (0, 0) := by
  cases characteristic_disj evr with
  | inl h => exact move_singular_point_to_origin_char2 evr e h hb2
  | inr h => cases h with
  | inl h => exact move_singular_point_to_origin_char3 evr e h hb2
  | inr h => exact move_singular_point_to_origin_bigchar evr e h


def pi_scaling (evr : EnatValRing p) (e : Model R) : Model R := {
  a1 := evr.sub_val e.a1 1,
  a2 := evr.sub_val e.a2 2,
  a3 := evr.sub_val e.a3 3,
  a4 := evr.sub_val e.a4 4,
  a6 := evr.sub_val e.a6 6 }

lemma pi_scaling_of_b2 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) :
  evr.sub_val e.b2 2 = evr.sub_val e.a1 1 * evr.sub_val e.a1 1 + 4 * evr.sub_val e.a2 2 := by
  rw [←evr.sub_val_mul_right h1, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val,
    ←evr.sub_val_mul_right h2, ←evr.sub_val_add _ _]
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn h1 h1
  . exact val_mul_ge_of_right_ge evr.valtn h2

lemma pi_scaling_of_b4 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4) :
  evr.sub_val e.b4 4 = evr.sub_val e.a1 1 * evr.sub_val e.a3 3 + 2 * evr.sub_val e.a4 4 := by
  rw [←evr.sub_val_mul_right h3, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val,
    ←evr.sub_val_mul_right h4, ←evr.sub_val_add _ _]
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn h1 h3
  . exact val_mul_ge_of_right_ge evr.valtn h4

lemma pi_scaling_of_b6 (evr : EnatValRing p) (e : Model R) (h3 : evr.valtn.v e.a3 ≥ 3)
  (h6 : evr.valtn.v e.a6 ≥ 6) :
  evr.sub_val e.b6 6 = evr.sub_val e.a3 3 * evr.sub_val e.a3 3 + 4 * evr.sub_val e.a6 6 := by
  rw [←evr.sub_val_mul_right h3, ←evr.sub_val_mul_left h3, evr.sub_val_sub_val,
    ←evr.sub_val_mul_right h6, ←evr.sub_val_add _ _]
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn h3 h3
  . exact val_mul_ge_of_right_ge evr.valtn h6

lemma pi_scaling_of_b8 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4)
  (h6 : evr.valtn.v e.a6 ≥ 6) :
  evr.sub_val e.b8 8 = evr.sub_val e.a1 1 * evr.sub_val e.a1 1 * evr.sub_val e.a6 6
    - evr.sub_val e.a1 1 * evr.sub_val e.a3 3 * evr.sub_val e.a4 4
    + 4 * evr.sub_val e.a2 2 * evr.sub_val e.a6 6
    + evr.sub_val e.a2 2 * evr.sub_val e.a3 3 * evr.sub_val e.a3 3
    - evr.sub_val e.a4 4 * evr.sub_val e.a4 4 :=
by
  rw [←evr.sub_val_mul_right h1, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val,
    ←evr.sub_val_mul_right h6, ←evr.sub_val_mul_left (val_mul_ge_of_both_ge evr.valtn h1 h1), evr.sub_val_sub_val]
  rw [←evr.sub_val_mul_right h3, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val,
    ←evr.sub_val_mul_right h4, ←evr.sub_val_mul_left (val_mul_ge_of_both_ge evr.valtn h1 h3), evr.sub_val_sub_val]
  rw [←evr.sub_val_mul_right h2, ←evr.sub_val_mul_right h6,
    ←evr.sub_val_mul_left (val_mul_ge_of_right_ge evr.valtn h2), evr.sub_val_sub_val]
  rw [←evr.sub_val_mul_left h2, ←evr.sub_val_mul_right h3, ←evr.sub_val_mul_right h3,
    evr.sub_val_sub_val, ←evr.sub_val_mul_left (val_mul_ge_of_both_ge evr.valtn h2 h3), evr.sub_val_sub_val]
  rw [←evr.sub_val_mul_right h4, ←evr.sub_val_mul_left h4, evr.sub_val_sub_val]
  have h116 := val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_both_ge evr.valtn h1 h1) h6
  have h134 := (val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_both_ge evr.valtn h1 h3) h4)
  have h26 := val_mul_ge_of_both_ge evr.valtn (@val_mul_ge_of_right_ge R _ (ofN 2) p evr.valtn 4 e.a2 h2) h6
  have h233 := val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_both_ge evr.valtn h2 h3) h3
  have h44 := val_mul_ge_of_both_ge evr.valtn h4 h4
  simp only [add_ofN] at h116 h134 h44 h26 h233
  rw [←val_neg] at h134
  rw [←val_neg] at h44

  rw [sub_eq_add_neg, sub_eq_add_neg, ←evr.sub_val_neg, ←evr.sub_val_neg,
    ←evr.sub_val_add h116 h134, ←evr.sub_val_add _ h26, ←evr.sub_val_add _ h233,
    ←evr.sub_val_add _ h44, ←sub_eq_add_neg, ←sub_eq_add_neg]
  . rfl
  . exact val_add_ge_of_ge evr.valtn
      (val_add_ge_of_ge evr.valtn (val_add_ge_of_ge evr.valtn h116 h134) h26) h233
  . exact val_add_ge_of_ge evr.valtn (val_add_ge_of_ge evr.valtn h116 h134) h26
  . exact val_add_ge_of_ge evr.valtn h116 h134

open EnatValRing in
lemma pi_scaling_of_discr (evr : EnatValRing p) (e : Model R)
  (hb2 : evr.valtn.v e.b2 ≥ 2) (hb4 : evr.valtn.v e.b4 ≥ 4)
  (hb6 : evr.valtn.v e.b6 ≥ 6) (hb8 : evr.valtn.v e.b8 ≥ 8) :
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
  . exact val_pow_ge_of_ge evr.valtn 3 hb4
  . norm_num
  . exact val_mul_ge_of_right_ge _ hb2
  . norm_num
  . exact val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_right_ge evr.valtn hb2) hb4
  . norm_num
  . exact val_mul_ge_of_right_ge evr.valtn hb6
  . norm_num
  . simpa
  . norm_num
  . exact val_mul_ge_of_both_ge evr.valtn (by simpa : SurjVal.v evr.valtn (-b2 e) ≥ 2) hb2
  . exact val_mul_ge_of_both_ge evr.valtn
      (val_mul_ge_of_both_ge evr.valtn (by simpa : SurjVal.v evr.valtn (-b2 e) ≥ 2) hb2) hb8
  . exact val_mul_ge_of_right_ge evr.valtn $ val_pow_ge_of_ge evr.valtn 3 hb4
  . apply val_sub_ge_of_ge
    . exact val_mul_ge_of_both_ge evr.valtn
        (val_mul_ge_of_both_ge evr.valtn (by simpa : SurjVal.v evr.valtn (-b2 e) ≥ 2) hb2) hb8
    . exact val_mul_ge_of_right_ge evr.valtn (val_pow_ge_of_ge evr.valtn 3 hb4)
  . exact val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_right_ge evr.valtn hb6) hb6
  . repeat' apply val_sub_ge_of_ge
    . exact val_mul_ge_of_both_ge evr.valtn
        (val_mul_ge_of_both_ge evr.valtn (by simpa : SurjVal.v evr.valtn (-b2 e) ≥ 2) hb2) hb8
    . apply val_mul_ge_of_right_ge evr.valtn
      exact val_pow_ge_of_ge evr.valtn 3 hb4
    . exact val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_right_ge evr.valtn hb6) hb6
  . exact val_mul_ge_of_both_ge
      evr.valtn (val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_right_ge evr.valtn hb2) hb4) hb6

lemma b2_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) : (pi_scaling evr e).b2 = evr.sub_val e.b2 2 := by
  simp only [b2, pi_scaling]
  exact (pi_scaling_of_b2 evr e h1 h2).symm

lemma b4_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4) :
  (pi_scaling evr e).b4 = evr.sub_val e.b4 4 := by
  simp only [b4, pi_scaling]
  exact (pi_scaling_of_b4 evr e h1 h3 h4).symm

lemma b6_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h3 : evr.valtn.v e.a3 ≥ 3)
  (h6 : evr.valtn.v e.a6 ≥ 6) :
  (pi_scaling evr e).b6 = evr.sub_val e.b6 6 := by
  simp only [b6, pi_scaling]
  exact (pi_scaling_of_b6 evr e h3 h6).symm

lemma b8_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4)
  (h6 : evr.valtn.v e.a6 ≥ 6) : (pi_scaling evr e).b8 = evr.sub_val e.b8 8 := by
  simp only [b8, pi_scaling]
  exact (pi_scaling_of_b8 evr e h1 h2 h3 h4 h6).symm

lemma val_b2_of_val_a12 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) : evr.valtn.v e.b2 ≥ 2 := by
  simp only [b2]
  apply val_add_ge_of_ge
  . apply val_mul_ge_of_both_ge evr.valtn h1 h1
  . apply val_mul_ge_of_right_ge evr.valtn h2

lemma val_b4_of_val_a134 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4) : evr.valtn.v e.b4 ≥ 4 := by
  simp only [b4]
  apply val_add_ge_of_ge
  . apply val_mul_ge_of_both_ge evr.valtn h1 h3
  . apply val_mul_ge_of_right_ge evr.valtn h4

lemma val_b6_of_val_a36 (evr : EnatValRing p) (e : Model R) (h3 : evr.valtn.v e.a3 ≥ 3)
  (h6 : evr.valtn.v e.a6 ≥ 6) : evr.valtn.v e.b6 ≥ 6 := by
  simp only [b6]
  apply val_add_ge_of_ge
  . apply val_mul_ge_of_both_ge evr.valtn h3 h3
  . apply val_mul_ge_of_right_ge evr.valtn h6

lemma val_b8_of_val_ai (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4)
  (h6 : evr.valtn.v e.a6 ≥ 6) : evr.valtn.v e.b8 ≥ 8 := by
  simp only [b8, sub_eq_add_neg]
  apply val_add_ge_of_ge
  . apply val_add_ge_of_ge
    . apply val_add_ge_of_ge
      . apply val_add_ge_of_ge
        . apply val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ h1 h1) h6
        . rw [val_neg]
          apply val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ h1 h3) h4
      . rw [mul_assoc]
        apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ h2 h6)
    . apply val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ h2 h3) h3
  . rw [val_neg]
    apply val_mul_ge_of_both_ge _ h4 h4

lemma discr_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) (h3 : evr.valtn.v e.a3 ≥ 3)
  (h4 : evr.valtn.v e.a4 ≥ 4) (h6 : evr.valtn.v e.a6 ≥ 6) :
  (pi_scaling evr e).discr = evr.sub_val e.discr 12 := by
  simp only [discr, b2_of_pi_scaling evr e h1 h2, b4_of_pi_scaling evr e h1 h3 h4,
    b6_of_pi_scaling evr e h3 h6, b8_of_pi_scaling evr e h1 h2 h3 h4 h6]
  exact (pi_scaling_of_discr evr e (val_b2_of_val_a12 evr e h1 h2)
    (val_b4_of_val_a134 evr e h1 h3 h4) (val_b6_of_val_a36 evr e h3 h6)
    (val_b8_of_val_ai evr e h1 h2 h3 h4 h6)).symm

lemma val_discr_of_val_ai (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4)
  (h6 : evr.valtn.v e.a6 ≥ 6) : evr.valtn.v e.discr ≥ 12 := by
  have hb2 := val_b2_of_val_a12 evr e h1 h2
  have hb4 := val_b4_of_val_a134 evr e h1 h3 h4
  have hb6 := val_b6_of_val_a36 evr e h3 h6
  have hb8 := val_b8_of_val_ai evr e h1 h2 h3 h4 h6
  simp only [discr, sub_eq_add_neg]
  repeat' apply val_add_ge_of_ge
  . rw [←neg_mul_left, ←neg_mul_left, val_neg]
    apply val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ hb2 hb2) hb8
  . rw [val_neg, pow_succ', pow_succ', pow_one]
    apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ hb4 hb4) hb4)
  . rw [val_neg, mul_assoc]
    apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ hb6 hb6)
  . rw [mul_assoc, mul_assoc]
    apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ hb2 (val_mul_ge_of_both_ge _ hb4 hb6))

end Model


namespace ValidModel

def pi_scaling (evr : EnatValRing p) (e : ValidModel R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4)
  (h6 : evr.valtn.v e.a6 ≥ 6) : ValidModel R := {
  toModel := Model.pi_scaling evr e.toModel,
  discr_not_zero := by
    rw [Model.discr_of_pi_scaling evr e.toModel h1 h2 h3 h4 h6]
    intro H
    have H' := let_value_eq (fun (x:R) => p ^ 12 * x) H
    simp only [mul_zero] at H'
    rw [←evr.factor_p_of_le_val (Model.val_discr_of_val_ai evr e.toModel h1 h2 h3 h4 h6)] at H'
    apply e.discr_not_zero H' }

lemma toModel_pi_scaling (evr : EnatValRing p) (e : ValidModel R) (h1 : evr.valtn.v e.a1 ≥ 1)
  (h2 : evr.valtn.v e.a2 ≥ 2) (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4)
  (h6 : evr.valtn.v e.a6 ≥ 6) :
  (e.pi_scaling evr h1 h2 h3 h4 h6).toModel = e.toModel.pi_scaling evr := rfl

def val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) : ℕ :=
nat_of_val valp e.discr_not_zero

@[simp]
lemma iso_rst_val_discr_to_nat {p : R} (valp : SurjVal p) (r s t : R) (e : ValidModel R) :
  val_discr_to_nat valp (rst_iso r s t e) = val_discr_to_nat valp e :=
by simp [val_discr_to_nat, nat_of_val, ValidModel.rst_iso, Model.rst_discr]


lemma ofN_val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) :
  val_discr_to_nat valp e = valp.v e.discr := by
  cases h : valp.v e.discr with
  | ofN n =>
    rwa [val_discr_to_nat, nat_of_val, ofN_to_nat_eq_self]
  | top =>
    exfalso
    rw [valp.v_eq_top_iff_zero] at h
    exact e.discr_not_zero h

lemma pi_scaling_val_discr_to_nat {p : R} (evr : EnatValRing p) (e : ValidModel R)
  (h1 : evr.valtn.v e.a1 ≥ 1) (h2 : evr.valtn.v e.a2 ≥ 2)
  (h3 : evr.valtn.v e.a3 ≥ 3) (h4 : evr.valtn.v e.a4 ≥ 4) (h6 : evr.valtn.v e.a6 ≥ 6) :
  val_discr_to_nat evr.valtn (pi_scaling evr e h1 h2 h3 h4 h6) = val_discr_to_nat evr.valtn e - 12 :=
by
  rw [Enat.eq_ofN, ofN_val_discr_to_nat, toModel_pi_scaling evr e h1 h2 h3 h4 h6,
    Model.discr_of_pi_scaling _ _ h1 h2 h3 h4 h6, evr.val_sub_val_eq]
  rw [ofN_val_discr_to_nat]

lemma v_b2_of_v_a1_a2 {p : R} (valp : SurjVal p) (e : ValidModel R) (h1 : valp.v e.a1 ≥ 1)
  (h2 : valp.v e.a2 = 1) : valp.v e.b2 ≥ 1 :=
  val_add_ge_of_ge valp (val_mul_ge_of_left_ge valp h1) (val_mul_ge_of_right_ge valp (le_of_eq h2.symm))

lemma v_b4_of_v_a1_a3_a4 {p : R} (valp : SurjVal p) (e : ValidModel R) (h1 : valp.v e.a1 ≥ 1)
  (h3 : valp.v e.a3 ≥ q) (h4 : valp.v e.a4 ≥ (q + 1)) : valp.v e.b4 ≥ (q + 1) := by
  apply val_add_ge_of_ge valp
  . rw [add_comm]
    exact (val_mul_ge_of_both_ge valp h1 h3)
  . exact (val_mul_ge_of_right_ge valp h4)

lemma v_b6_of_v_a3_a6 {p : R} {q : ℕ} (valp : SurjVal p) (e : ValidModel R) (h3 : valp.v e.a3 ≥ q)
  (h6 : valp.v e.a6 ≥ ↑(2 * q)) : valp.v e.b6 ≥ ↑(2 * q) := by
  apply val_add_ge_of_ge valp
  . rw [←add_self_eq_mul_two q]
    exact (val_mul_ge_of_both_ge valp h3 h3)
  . exact (val_mul_ge_of_right_ge valp h6)

lemma v_b8_of_v_ai {p : R} {q : ℕ} (valp : SurjVal p) (e : ValidModel R) (h1 : valp.v e.a1 ≥ 1)
  (h2 : valp.v e.a2 = 1) (h3 : valp.v e.a3 ≥ q) (h4 : valp.v e.a4 ≥ (q + 1))
  (h6 : valp.v e.a6 ≥ ↑(2 * q)) : valp.v e.b8 ≥ ↑(2 * q + 1) := by
  simp only [Model.b8]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  repeat apply val_add_ge_of_ge valp
  . rw [mul_assoc, Nat.add_comm]
    exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h1 h6)
  . rw [val_neg, mul_assoc, ←add_self_eq_mul_two q, Nat.add_assoc]
    exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h3 h4)
  . rw [mul_assoc, Nat.add_comm]
    exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp (le_of_eq h2.symm) h6)
  . rw [mul_assoc, ←add_self_eq_mul_two q, Nat.add_comm]
    exact val_mul_ge_of_both_ge valp (le_of_eq h2.symm) (val_mul_ge_of_both_ge valp h3 h3)
  . rw [val_neg, ←add_self_eq_mul_two q, Nat.add_assoc]
    exact val_mul_ge_of_both_ge valp (le_trans (le_succ (ofN q)) h4) h4


lemma v_discr_of_v_ai {p : R} {q : ℕ} (valp : SurjVal p) (e : ValidModel R) (hq : q > 1)
  (h1 : valp.v e.a1 ≥ 1) (h2 : valp.v e.a2 = 1) (h3 : valp.v e.a3 ≥ q)
  (h4 : valp.v e.a4 ≥ (q + 1)) (h6 : valp.v e.a6 ≥ ↑(2 * q)) :
  valp.v e.discr ≥ ↑(2 * q + 3) := by
  have h2' := v_b2_of_v_a1_a2 valp e h1 h2
  have h4' := v_b4_of_v_a1_a3_a4 valp e h1 h3 h4
  have h6' := v_b6_of_v_a3_a6 valp e h3 h6
  have h8' := v_b8_of_v_ai valp e h1 h2 h3 h4 h6
  simp only [Model.discr]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  repeat' apply val_add_ge_of_ge valp
  . rw [←neg_mul_left, ←neg_mul_left, val_neg, (show 3 = 1 + 1 + 1 by rfl), ←Nat.add_assoc,
      ←Nat.add_assoc, Nat.add_assoc, mul_comm]
    exact val_mul_ge_of_both_ge valp h8' (val_mul_ge_of_both_ge valp h2' h2')
  . rw [val_neg, pow_succ', pow_succ', pow_one, ←add_self_eq_mul_two,
      (show q + q + 3 = q + 1 + (q + 1) + 1 by ring)]
    exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp
      (val_mul_ge_of_both_ge valp h4' h4') (le_trans ((le_ofN _ _).1 (Nat.le_add_left 1 q)) h4'))
  . rw [val_neg, mul_assoc, (show 3 = 2 + 1 by rfl)]
    apply val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h6' (le_trans ((le_ofN _ _).1 _) h6'))
    rw [←add_self_eq_mul_two q]
    exact Nat.add_le_add (Nat.succ_le_of_lt hq) (Nat.le_of_lt hq)
  . rw [(show 3 = 1 + (1 + 1) by rfl), mul_comm, mul_assoc 9]
    exact val_mul_ge_of_both_ge valp h6' (val_mul_ge_of_right_ge valp
      (val_mul_ge_of_both_ge valp h2' (le_trans ((le_ofN _ _).1
      (Nat.add_le_add (Nat.le_of_lt hq) (le_of_eq rfl))) h4')))

lemma small_char_div_12 {p : R} (hp : p = 2 ∨ p = 3) (valp : SurjVal p) : valp.v 12 ≥ 1 := by
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


lemma v_rst_b2_of_small_char {p : R} (valp : SurjVal p) (e : ValidModel R) (r s t : R)
  (h_b2 : valp.v e.b2 ≥ 1) (h_p : valp.v 12 ≥ 1) : valp.v (rst_iso r s t e).b2 ≥ 1 := by
  simp only [rst_iso]
  rw [Model.rst_b2]
  apply val_add_ge_of_ge valp h_b2
  exact val_mul_ge_of_left_ge valp h_p

section cubic

def Δcubic (c : R × R × R) : R :=
18 * c.1 * c.2.1 * c.2.2 - 4 * c.1 ^ 3 * c.2.2 + c.1 ^ 2 * c.2.1 ^ 2 - 4 * c.2.1 ^ 3 - 27 * c.2.2 ^ 2

def model_to_cubic {p : R} (evr : EnatValRing p) (e : ValidModel R) : R × R × R :=
(evr.sub_val e.a2 1, evr.sub_val e.a4 2, evr.sub_val e.a6 3)

def cubic_has_distinct_roots {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
evr.valtn.v (Δcubic (model_to_cubic evr e)) = 0

def δmultiplicity (c : R × R × R) : R := 3 * c.2.1 - c.1 ^ 2

def cubic_has_double_root {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
evr.valtn.v (Δcubic (model_to_cubic evr e)) > 0 ∧ evr.valtn.v (δmultiplicity (model_to_cubic evr e)) = 0

def cubic_has_triple_root {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
evr.valtn.v (Δcubic (model_to_cubic evr e)) > 0 ∧ evr.valtn.v (δmultiplicity (model_to_cubic evr e)) > 0

def move_cubic_double_root_to_origin_iso {p : R} (evr : EnatValRing p) (e : ValidModel R) : ValidModel R :=
  let (a2p, a4p2, _) := model_to_cubic evr e
  rst_iso (p * evr.lift (if evr.residue.char = 2 then a4p2 else a2p * a4p2)) 0 0 e

def cubic_double_root_is_zero {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
  let (a2p, a4p2, a6p3) := model_to_cubic evr e
  evr.valtn.v a2p = 0 ∧ evr.valtn.v a4p2 > 0 ∧ evr.valtn.v a6p3 > 0

lemma move_cubic_double_root_to_origin {p : R} (evr : EnatValRing p) (e : ValidModel R) :
  cubic_has_double_root evr e → cubic_double_root_is_zero evr (move_cubic_double_root_to_origin_iso evr e) := sorry

def move_cubic_triple_root_to_origin_iso {p : R} (evr : EnatValRing p) (e : ValidModel R) : ValidModel R :=
  let (a2p, _, a6p3) := model_to_cubic evr e
  rst_iso (p * evr.lift (if evr.residue.char = 2 then -a2p else -a6p3)) 0 0 e

def cubic_triple_root_is_zero {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
  let (a2p, a4p2, a6p3) := model_to_cubic evr e
  evr.valtn.v a2p > 0 ∧ evr.valtn.v a4p2 > 0 ∧ evr.valtn.v a6p3 > 0

lemma move_cubic_triple_root_to_origin {p : R} (evr : EnatValRing p) (e : ValidModel R) :
cubic_has_triple_root evr e → cubic_triple_root_is_zero evr (move_cubic_triple_root_to_origin_iso evr e) := sorry

end cubic


end ValidModel
