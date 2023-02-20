import ECTate.Algebra.EllipticCurve.Kronecker
import ECTate.Algebra.EllipticCurve.Model
import ECTate.Algebra.ValuedRing
import ECTate.Data.Nat.Enat
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Contrapose
import Aesop
import Mathlib.Tactic.Linarith
import ECTate.Algebra.ResidueRing
-- import Mathlib.Algebra.Order.Field.Defs

open Enat

variable {R : Type u} [CommRing R] [inst : IsDomain R]


namespace Model

variable {p : R}

def is_local_singular_point (valp : SurjVal p) (e : Model R) (P : R × R) : Prop :=
valp (weierstrass e P) > 0 ∧ valp (dweierstrass_dx e P) > 0 ∧ valp (dweierstrass_dy e P) > 0

lemma mk'_apply [NonAssocRing R] (x : R) (c : RingCon R) : c.mk' x = x := rfl
lemma is_local_singular_point_iff (evr : EnatValRing p) (e : Model R) (P : R × R) :
  is_local_singular_point evr.valtn e P ↔ is_singular_point (e.map evr.RingCon.mk') (P.map evr.RingCon.mk' evr.RingCon.mk')
  := by
  rw [is_singular_point]
  rw [weierstrass_map, dweierstrass_dx_map, dweierstrass_dy_map]
  simp [mk'_apply]
  rw [← RingCon.coe_zero]
  rw [RingCon.eq, RingCon.rel_mk, SurjVal.s.r_eq, congruence_p]
  rw [RingCon.eq, RingCon.rel_mk, SurjVal.s.r_eq, congruence_p]
  rw [RingCon.eq, RingCon.rel_mk, SurjVal.s.r_eq, congruence_p]
  simp
  rfl

lemma singular_of_val_discr (valp : SurjVal p) (e : Model R) (h : valp e.discr > 0) :
  ∃ P, is_local_singular_point valp e P :=
by
  sorry

def singular_point_on_special [DecidableEq R] (evr : EnatValRing p) (e : Model R) : R × R :=
  if e.c4 = 0 then
    match evr.residue_char with
    | 2 => (evr.pth_root e.a4, evr.pth_root (e.a2 * e.a4 + e.a6))
    | 3 => (evr.pth_root (-(e.a3 ^ 2) - e.a6), e.a1 * evr.pth_root (-(e.a3 ^ 2) - e.a6) + e.a3)
    | _ => (-e.b2 * evr.inv_mod 12, -(-e.a1 * e.b2 * evr.inv_mod 12 + e.a3) * evr.inv_mod 2)
  else
    ((18 * e.b6 - e.b2 * e.b4) * evr.inv_mod e.c4, (e.b2 * e.b5 + 3 * e.b7) * evr.inv_mod e.c4)

def move_singular_point_to_origin_triple [DecidableEq R] (evr : EnatValRing p) (e : Model R) : R × R × R :=
⟨(singular_point_on_special evr e).1, 0, (singular_point_on_special evr e).2⟩

-- def move_singular_point_to_origin_iso [DecidableEq R] (evr : EnatValRing p) (e : Model R) : R × R × R :=
--   match evr.residue_char with
--   | 2 => (evr.norm_repr e.a4, 0, evr.norm_repr (e.a6 + e.a4 * e.a2))
--   | 3 => (evr.norm_repr (-e.b6), 0, evr.norm_repr (e.a3 - e.b6 * e.a1))
--   | _ => (0, 0, 0) --need to fill here

-- def move_singular_point_to_origin_iso [DecidableEq R] (evr : EnatValRing p) (e : Model R) : R × R × R :=
-- rst_triple e (move_singular_point_to_origin_triple e)

def move_singular_point_to_origin_iso [DecidableEq R] (evr : EnatValRing p) (e : Model R) :
  Model R :=
rst_triple e (move_singular_point_to_origin_triple evr e)

lemma move_singular_point_to_origin [DecidableEq R] (evr : EnatValRing p) (e : Model R) :
(∃ P, is_local_singular_point evr.valtn e P) →
  is_local_singular_point evr.valtn (move_singular_point_to_origin_iso evr e) (0, 0) :=
by
  rintro ⟨P, h⟩
  have  := Model.Field.move_singular_point_to_origin' (e.map evr.RingCon.mk') ⟨P.map evr.RingCon.mk' evr.RingCon.mk', ?_⟩
  . rw [is_local_singular_point_iff]
    simp
    convert this
    simp [move_singular_point_to_origin_iso, Field.move_singular_point_to_origin_iso,
          move_singular_point_to_origin_triple, Field.move_singular_point_to_origin_triple]
    sorry
  . rwa [is_local_singular_point_iff] at h



def pi_scaling (evr : EnatValRing p) (e : Model R) : Model R := {
  a1 := evr.sub_val 1 e.a1,
  a2 := evr.sub_val 2 e.a2,
  a3 := evr.sub_val 3 e.a3,
  a4 := evr.sub_val 4 e.a4,
  a6 := evr.sub_val 6 e.a6 }

lemma pi_scaling_of_b2 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) :
  evr.sub_val 2 e.b2 = evr.sub_val 1 e.a1 * evr.sub_val 1 e.a1 + 4 * evr.sub_val 2 e.a2 := by
  rw [←evr.sub_val_mul_right h1, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val,
    ←evr.sub_val_mul_right h2, ←evr.sub_val_add _ _]
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn h1 h1
  . exact val_mul_ge_of_right_ge evr.valtn h2

lemma pi_scaling_of_b4 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4) :
  evr.sub_val 4 e.b4 = evr.sub_val 1 e.a1 * evr.sub_val 3 e.a3 + 2 * evr.sub_val 4 e.a4 := by
  rw [←evr.sub_val_mul_right h3, ←evr.sub_val_mul_left h1, evr.sub_val_sub_val,
    ←evr.sub_val_mul_right h4, ←evr.sub_val_add _ _]
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn h1 h3
  . exact val_mul_ge_of_right_ge evr.valtn h4

lemma pi_scaling_of_b6 (evr : EnatValRing p) (e : Model R) (h3 : evr.valtn e.a3 ≥ 3)
  (h6 : evr.valtn e.a6 ≥ 6) :
  evr.sub_val 6 e.b6 = evr.sub_val 3 e.a3 * evr.sub_val 3 e.a3 + 4 * evr.sub_val 6 e.a6 := by
  rw [←evr.sub_val_mul_right h3, ←evr.sub_val_mul_left h3, evr.sub_val_sub_val,
    ←evr.sub_val_mul_right h6, ←evr.sub_val_add _ _]
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn h3 h3
  . exact val_mul_ge_of_right_ge evr.valtn h6

lemma pi_scaling_of_b8 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4)
  (h6 : evr.valtn e.a6 ≥ 6) :
  evr.sub_val 8 e.b8 = evr.sub_val 1 e.a1 * evr.sub_val 1 e.a1 * evr.sub_val 6 e.a6
    - evr.sub_val 1 e.a1 * evr.sub_val 3 e.a3 * evr.sub_val 4 e.a4
    + 4 * evr.sub_val 2 e.a2 * evr.sub_val 6 e.a6
    + evr.sub_val 2 e.a2 * evr.sub_val 3 e.a3 * evr.sub_val 3 e.a3
    - evr.sub_val 4 e.a4 * evr.sub_val 4 e.a4 :=
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
  have h26 := val_mul_ge_of_both_ge evr.valtn (@val_mul_ge_of_right_ge R _ _ 2 p evr.valtn 4 e.a2 h2) h6
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
  (hb2 : evr.valtn e.b2 ≥ 2) (hb4 : evr.valtn e.b4 ≥ 4)
  (hb6 : evr.valtn e.b6 ≥ 6) (hb8 : evr.valtn e.b8 ≥ 8) :
  evr.sub_val 12 e.discr = -evr.sub_val 2 e.b2 * evr.sub_val 2 e.b2 * evr.sub_val 8 e.b8
    - 8 * ((evr.sub_val 4 e.b4) ^ 3) - 27 * evr.sub_val 6 e.b6 * evr.sub_val 6 e.b6
    + 9 * evr.sub_val 2 e.b2 * evr.sub_val 4 e.b4 * evr.sub_val 6 e.b6 :=
by
  rw [discr,
      sub_val_add,
      sub_val_sub,
      sub_val_sub,
      sub_val_mul _ _ _ _ _ hb8,
      sub_val_mul _ _ _ _ _ hb2,
      sub_val_mul _ _ _ _ _ hb6,
      sub_val_mul_right _ hb6,
      sub_val_mul _ _ _ _ _ hb6,
      sub_val_mul _ _ _ _ _ hb4,
      sub_val_mul_right _ hb2,
      sub_val_mul_right,
      sub_val_pow _ _ _ _ hb4,
      sub_val_neg]
  . rfl
  . exact val_pow_ge_of_ge evr.valtn 3 hb4
  swap
  . rfl
  . exact val_mul_ge_of_right_ge _ hb2
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_right_ge evr.valtn hb2) hb4
  . rfl
  . exact val_mul_ge_of_right_ge evr.valtn hb6
  swap
  . rfl
  . simpa
  . rfl
  . exact val_mul_ge_of_both_ge evr.valtn (by simpa : evr.valtn (-b2 e) ≥ 2) hb2
  . exact val_mul_ge_of_both_ge evr.valtn
      (val_mul_ge_of_both_ge evr.valtn (by simpa : evr.valtn (-b2 e) ≥ 2) hb2) hb8
  . exact val_mul_ge_of_right_ge evr.valtn $ val_pow_ge_of_ge evr.valtn 3 hb4
  . apply val_sub_ge_of_ge
    . exact val_mul_ge_of_both_ge evr.valtn
        (val_mul_ge_of_both_ge evr.valtn (by simpa : evr.valtn (-b2 e) ≥ 2) hb2) hb8
    . exact val_mul_ge_of_right_ge evr.valtn (val_pow_ge_of_ge evr.valtn 3 hb4)
  . exact val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_right_ge evr.valtn hb6) hb6
  . repeat' apply val_sub_ge_of_ge
    . simp [-ge_iff_le, evr.valtn.v_mul_eq_add_v]
      cases h : evr.valtn (b2 e)
      . simp [-ge_iff_le]
        cases h' : evr.valtn (b8 e)
        . simp [-ge_iff_le]
          norm_cast
          sorry
        . simp
      . simp
      -- refine val_mul_ge_of_both_ge evr.valtn
      --   (val_mul_ge_of_both_ge evr.valtn ?_ hb2) hb8

    . apply val_mul_ge_of_right_ge evr.valtn
      exact val_pow_ge_of_ge evr.valtn 3 hb4
    . exact val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_right_ge evr.valtn hb6) hb6
  . exact val_mul_ge_of_both_ge
      evr.valtn (val_mul_ge_of_both_ge evr.valtn (val_mul_ge_of_right_ge evr.valtn hb2) hb4) hb6

lemma b2_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) : (pi_scaling evr e).b2 = evr.sub_val 2 e.b2 := by
  simp only [b2, pi_scaling]
  exact (pi_scaling_of_b2 evr e h1 h2).symm

lemma b4_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4) :
  (pi_scaling evr e).b4 = evr.sub_val 4 e.b4 := by
  simp only [b4, pi_scaling]
  exact (pi_scaling_of_b4 evr e h1 h3 h4).symm

lemma b6_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h3 : evr.valtn e.a3 ≥ 3)
  (h6 : evr.valtn e.a6 ≥ 6) :
  (pi_scaling evr e).b6 = evr.sub_val 6 e.b6 := by
  simp only [b6, pi_scaling]
  exact (pi_scaling_of_b6 evr e h3 h6).symm

lemma b8_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4)
  (h6 : evr.valtn e.a6 ≥ 6) : (pi_scaling evr e).b8 = evr.sub_val 8 e.b8 := by
  simp only [b8, pi_scaling]
  exact (pi_scaling_of_b8 evr e h1 h2 h3 h4 h6).symm

lemma val_b2_of_val_a12 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) : evr.valtn e.b2 ≥ 2 := by
  simp only [b2]
  apply val_add_ge_of_ge
  . apply val_mul_ge_of_both_ge evr.valtn h1 h1
  . apply val_mul_ge_of_right_ge evr.valtn h2

lemma val_b4_of_val_a134 (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4) : evr.valtn e.b4 ≥ 4 := by
  simp only [b4]
  apply val_add_ge_of_ge
  . apply val_mul_ge_of_both_ge evr.valtn h1 h3
  . apply val_mul_ge_of_right_ge evr.valtn h4

lemma val_b6_of_val_a36 (evr : EnatValRing p) (e : Model R) (h3 : evr.valtn e.a3 ≥ 3)
  (h6 : evr.valtn e.a6 ≥ 6) : evr.valtn e.b6 ≥ 6 := by
  simp only [b6]
  apply val_add_ge_of_ge
  . apply val_mul_ge_of_both_ge evr.valtn h3 h3
  . apply val_mul_ge_of_right_ge evr.valtn h6

lemma val_b8_of_val_ai (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4)
  (h6 : evr.valtn e.a6 ≥ 6) : evr.valtn e.b8 ≥ 8 := by
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

lemma discr_of_pi_scaling (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) (h3 : evr.valtn e.a3 ≥ 3)
  (h4 : evr.valtn e.a4 ≥ 4) (h6 : evr.valtn e.a6 ≥ 6) :
  (pi_scaling evr e).discr = evr.sub_val 12 e.discr := by
  simp only [discr, b2_of_pi_scaling evr e h1 h2, b4_of_pi_scaling evr e h1 h3 h4,
    b6_of_pi_scaling evr e h3 h6, b8_of_pi_scaling evr e h1 h2 h3 h4 h6]
  exact (pi_scaling_of_discr evr e (val_b2_of_val_a12 evr e h1 h2)
    (val_b4_of_val_a134 evr e h1 h3 h4) (val_b6_of_val_a36 evr e h3 h6)
    (val_b8_of_val_ai evr e h1 h2 h3 h4 h6)).symm

lemma val_discr_of_val_ai (evr : EnatValRing p) (e : Model R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4)
  (h6 : evr.valtn e.a6 ≥ 6) : evr.valtn e.discr ≥ 12 := by
  have hb2 := val_b2_of_val_a12 evr e h1 h2
  have hb4 := val_b4_of_val_a134 evr e h1 h3 h4
  have hb6 := val_b6_of_val_a36 evr e h3 h6
  have hb8 := val_b8_of_val_ai evr e h1 h2 h3 h4 h6
  simp only [discr, sub_eq_add_neg]
  repeat' apply val_add_ge_of_ge
  . rw [←neg_mul_eq_neg_mul, ←neg_mul_eq_neg_mul, val_neg]
    apply val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ hb2 hb2) hb8
  . rw [val_neg, pow_succ', pow_succ', pow_one]
    apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ (val_mul_ge_of_both_ge _ hb4 hb4) hb4)
  . rw [val_neg, mul_assoc]
    apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ hb6 hb6)
  . rw [mul_assoc, mul_assoc]
    apply val_mul_ge_of_right_ge _ (val_mul_ge_of_both_ge _ hb2 (val_mul_ge_of_both_ge _ hb4 hb6))

end Model


namespace ValidModel

def pi_scaling (evr : EnatValRing p) (e : ValidModel R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4)
  (h6 : evr.valtn e.a6 ≥ 6) : ValidModel R := {
  toModel := Model.pi_scaling evr e.toModel,
  discr_not_zero := by
    rw [Model.discr_of_pi_scaling evr e.toModel h1 h2 h3 h4 h6]
    intro H
    have H' := let_value_eq (fun (x:R) => p ^ 12 * x) H
    simp only [mul_zero] at H'
    rw [←evr.factor_p_of_le_val (Model.val_discr_of_val_ai evr e.toModel h1 h2 h3 h4 h6)] at H'
    apply e.discr_not_zero H' }

lemma toModel_pi_scaling (evr : EnatValRing p) (e : ValidModel R) (h1 : evr.valtn e.a1 ≥ 1)
  (h2 : evr.valtn e.a2 ≥ 2) (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4)
  (h6 : evr.valtn e.a6 ≥ 6) :
  (e.pi_scaling evr h1 h2 h3 h4 h6).toModel = e.toModel.pi_scaling evr := rfl

def val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) : ℕ :=
nat_of_val valp e.discr_not_zero

@[simp]
lemma iso_rst_val_discr_to_nat {p : R} (valp : SurjVal p) (r s t : R) (e : ValidModel R) :
  val_discr_to_nat valp (rst_iso r s t e) = val_discr_to_nat valp e :=
by simp [val_discr_to_nat, nat_of_val, ValidModel.rst_iso, Model.rst_discr]


lemma ofN_val_discr_to_nat {p : R} (valp : SurjVal p) (e : ValidModel R) :
  val_discr_to_nat valp e = valp e.discr := by
  cases h : valp e.discr with
  | ofN n =>
    rwa [val_discr_to_nat, nat_of_val, ofN_to_nat_eq_self]
  | top =>
    exfalso
    rw [valp.v_eq_top_iff_zero] at h
    exact e.discr_not_zero h

lemma pi_scaling_val_discr_to_nat {p : R} (evr : EnatValRing p) (e : ValidModel R)
  (h1 : evr.valtn e.a1 ≥ 1) (h2 : evr.valtn e.a2 ≥ 2)
  (h3 : evr.valtn e.a3 ≥ 3) (h4 : evr.valtn e.a4 ≥ 4) (h6 : evr.valtn e.a6 ≥ 6) :
  val_discr_to_nat evr.valtn (pi_scaling evr e h1 h2 h3 h4 h6) = val_discr_to_nat evr.valtn e - 12 :=
by
  rw [Enat.eq_ofN, ofN_val_discr_to_nat, toModel_pi_scaling evr e h1 h2 h3 h4 h6,
    Model.discr_of_pi_scaling _ _ h1 h2 h3 h4 h6, evr.val_sub_val_eq]
  rw [ofN_val_discr_to_nat]

lemma v_b2_of_v_a1_a2 {p : R} (valp : SurjVal p) (e : ValidModel R) (h1 : valp e.a1 ≥ 1)
  (h2 : valp e.a2 = 1) : valp e.b2 ≥ 1 :=
  val_add_ge_of_ge valp (val_mul_ge_of_left_ge valp h1) (val_mul_ge_of_right_ge valp (le_of_eq h2.symm))

lemma v_b4_of_v_a1_a3_a4 {p : R} (valp : SurjVal p) (e : ValidModel R) (h1 : valp e.a1 ≥ 1)
  (h3 : valp e.a3 ≥ q) (h4 : valp e.a4 ≥ (q + 1)) : valp e.b4 ≥ (q + 1) := by
  apply val_add_ge_of_ge valp
  . rw [add_comm]
    exact (val_mul_ge_of_both_ge valp h1 h3)
  . exact (val_mul_ge_of_right_ge valp h4)

lemma v_b6_of_v_a3_a6 {p : R} {q : ℕ} (valp : SurjVal p) (e : ValidModel R) (h3 : valp e.a3 ≥ q)
  (h6 : valp e.a6 ≥ ↑(2 * q)) : valp e.b6 ≥ ↑(2 * q) := by
  apply val_add_ge_of_ge valp
  . rw [←add_self_eq_mul_two q]
    exact (val_mul_ge_of_both_ge valp h3 h3)
  . exact (val_mul_ge_of_right_ge valp h6)

lemma v_b8_of_v_ai {p : R} {q : ℕ} (valp : SurjVal p) (e : ValidModel R) (h1 : valp e.a1 ≥ 1)
  (h2 : valp e.a2 = 1) (h3 : valp e.a3 ≥ q) (h4 : valp e.a4 ≥ (q + 1))
  (h6 : valp e.a6 ≥ ↑(2 * q)) : valp e.b8 ≥ ↑(2 * q + 1) := by
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
  (h1 : valp e.a1 ≥ 1) (h2 : valp e.a2 = 1) (h3 : valp e.a3 ≥ q)
  (h4 : valp e.a4 ≥ (q + 1)) (h6 : valp e.a6 ≥ ↑(2 * q)) :
  valp e.discr ≥ ↑(2 * q + 3) := by
  have h2' := v_b2_of_v_a1_a2 valp e h1 h2
  have h4' := v_b4_of_v_a1_a3_a4 valp e h1 h3 h4
  have h6' := v_b6_of_v_a3_a6 valp e h3 h6
  have h8' := v_b8_of_v_ai valp e h1 h2 h3 h4 h6
  simp only [Model.discr]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  repeat' apply val_add_ge_of_ge valp
  . rw [←neg_mul_eq_neg_mul, ←neg_mul_eq_neg_mul, val_neg, (show 3 = 1 + 1 + 1 by rfl), ←Nat.add_assoc,
      ←Nat.add_assoc, Nat.add_assoc, mul_comm]
    exact val_mul_ge_of_both_ge valp h8' (val_mul_ge_of_both_ge valp h2' h2')
  . rw [val_neg, pow_succ', pow_succ', pow_one, ←add_self_eq_mul_two,
      (show q + q + 3 = q + 1 + (q + 1) + 1 by ring)]
    exact val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp
      (val_mul_ge_of_both_ge valp h4' h4') (le_trans ((le_ofN _ _).2 (Nat.le_add_left 1 q)) h4'))
  . rw [val_neg, mul_assoc, (show 3 = 2 + 1 by rfl)]
    apply val_mul_ge_of_right_ge valp (val_mul_ge_of_both_ge valp h6' (le_trans ((le_ofN _ _).2 _) h6'))
    rw [←add_self_eq_mul_two q]
    exact Nat.add_le_add (Nat.succ_le_of_lt hq) (Nat.le_of_lt hq)
  . rw [(show 3 = 1 + (1 + 1) by rfl), mul_comm, mul_assoc 9]
    exact val_mul_ge_of_both_ge valp h6' (val_mul_ge_of_right_ge valp
      (val_mul_ge_of_both_ge valp h2' (le_trans ((le_ofN _ _).2
      (Nat.add_le_add (Nat.le_of_lt hq) (le_of_eq rfl))) h4')))

lemma small_char_div_12 {p : R} (hp : p = 2 ∨ p = 3) (valp : SurjVal p) : valp 12 ≥ 1 := by
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
  (h_b2 : valp e.b2 ≥ 1) (h_p : valp 12 ≥ 1) : valp (rst_iso r s t e).b2 ≥ 1 := by
  simp only [rst_iso]
  -- aesop
  rw [Model.rst_b2]
  apply val_add_ge_of_ge valp h_b2
  exact val_mul_ge_of_left_ge valp h_p

section cubic

def Δcubic (c : R × R × R) : R :=
18 * c.1 * c.2.1 * c.2.2 - 4 * c.1 ^ 3 * c.2.2 + c.1 ^ 2 * c.2.1 ^ 2 - 4 * c.2.1 ^ 3 - 27 * c.2.2 ^ 2

def model_to_cubic {p : R} (evr : EnatValRing p) (e : ValidModel R) : R × R × R :=
(evr.sub_val 1 e.a2, evr.sub_val 2 e.a4, evr.sub_val 3 e.a6)

def cubic_has_distinct_roots {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
evr.valtn (Δcubic (model_to_cubic evr e)) = 0

def δmultiplicity (c : R × R × R) : R := 3 * c.2.1 - c.1 ^ 2

def cubic_has_double_root {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
evr.valtn (Δcubic (model_to_cubic evr e)) > 0 ∧ evr.valtn (δmultiplicity (model_to_cubic evr e)) = 0

def cubic_has_triple_root {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
evr.valtn (Δcubic (model_to_cubic evr e)) > 0 ∧ evr.valtn (δmultiplicity (model_to_cubic evr e)) > 0

def move_cubic_double_root_to_origin_iso {p : R} (evr : EnatValRing p) (e : ValidModel R) : ValidModel R :=
  let (a2p, a4p2, _) := model_to_cubic evr e
  rst_iso (p * (evr.norm_repr (if evr.residue_char = 2 then a4p2 else a2p * a4p2))) 0 0 e

def cubic_double_root_is_zero {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
  let (a2p, a4p2, a6p3) := model_to_cubic evr e
  evr.valtn a2p = 0 ∧ evr.valtn a4p2 > 0 ∧ evr.valtn a6p3 > 0

lemma move_cubic_double_root_to_origin {p : R} (evr : EnatValRing p) (e : ValidModel R) :
  cubic_has_double_root evr e → cubic_double_root_is_zero evr (move_cubic_double_root_to_origin_iso evr e) := sorry

def move_cubic_triple_root_to_origin_iso {p : R} (evr : EnatValRing p) (e : ValidModel R) : ValidModel R :=
  let (a2p, _, a6p3) := model_to_cubic evr e
  rst_iso (p * (evr.norm_repr (if evr.residue_char = 2 then -a2p else -a6p3))) 0 0 e

def cubic_triple_root_is_zero {p : R} (evr : EnatValRing p) (e : ValidModel R) : Prop :=
  let (a2p, a4p2, a6p3) := model_to_cubic evr e
  evr.valtn a2p > 0 ∧ evr.valtn a4p2 > 0 ∧ evr.valtn a6p3 > 0

lemma move_cubic_triple_root_to_origin {p : R} (evr : EnatValRing p) (e : ValidModel R) :
cubic_has_triple_root evr e → cubic_triple_root_is_zero evr (move_cubic_triple_root_to_origin_iso evr e) := sorry

end cubic


end ValidModel
