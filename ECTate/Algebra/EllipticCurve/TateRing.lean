import ECTate.Algebra.EllipticCurve.AuxRingLemmas
import ECTate.Algebra.EllipticCurve.Kronecker
import ECTate.Algebra.EllipticCurve.Model
import ECTate.Algebra.ValuedRing
import ECTate.Algebra.EllipticCurve.LocalEC
import ECTate.Algebra.EllipticCurve.KodairaTypes
import ECTate.Data.Nat.Enat
import Mathlib.Tactic.LibrarySearch
import Mathlib.Init.Algebra.Order
import Mathlib.Data.Int.Basic

open ValidModel
open Enat
open Kodaira
open EnatValRing
open SurjVal


def kodaira_type_Is
  {R : Type u}
[Repr R] -- TODO delete
  [DecidableEq R] [CommRing R] [IsDomain R] {π : R}
  (evr : EnatValRing π) (e : ValidModel R) (u0 r0 s0 t0 : R) (m q : ℕ)
  (hq : 1 < q) (h1 : evr.valtn e.a1 ≥ 1) (h2 : evr.valtn e.a2 = 1)
  (h3 : evr.valtn e.a3 ≥ q) (h4 : evr.valtn e.a4 ≥ q + 1)
  (h6 : evr.valtn e.a6 ≥ 2 * q) :
  ℕ × ℕ × R × R :=
  let evrp := evr
  let surjvalp := evrp.valtn
  let (r, t) := (r0, t0)
  let a3q := sub_val evrp q e.a3
  let a6q2 := sub_val evrp (2 * q) e.a6
  have rw_a6 : sub_val evrp (2 * q) e.a6 = a6q2 := rfl --obvious rewriting lemmas that Lean should generate implicitly

  if discr_1 : surjvalp (a3q ^ 2 + 4 * a6q2) = 0 then
    let c := if evrp.quad_roots_in_residue_field 1 a3q (-a6q2) then 4 else 2
    (m, c, (r, t))
  else
  have hdr : evrp.has_double_root 1 a3q (-a6q2) := by
    apply And.intro (val_of_one surjvalp) _
    apply Enat.pos_of_ne_zero
    rw [mul_one, ←neg_mul_eq_mul_neg, sub_eq_add_neg, neg_neg]
    exact discr_1
  let a := evrp.double_root 1 a3q (-a6q2)

  let e1 := rst_iso 0 0 (a * (π ^ q)) e
  -- dbg_trace (_root_.repr e1)
  have h1' : surjvalp e1.a1 ≥ 1 := by rwa [rt_of_a1]
  have h2' : surjvalp e1.a2 = 1 := by rwa [t_of_a2]
  have h3' : surjvalp e1.a3 ≥ q + 1 := by
    rw [t_of_a3, evrp.factor_p_of_le_val h3, ←mul_assoc, mul_comm (2*a),
      ←mul_add, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer]
    apply add_le_add (le_of_eq rfl)
    rw [add_comm, ←mul_one 2]
    exact succ_le_of_lt (val_poly_of_double_root evrp 1 a3q (-a6q2) hdr).2
  have h4' : surjvalp e1.a4 ≥ q + 1 := by
    rw [t_of_a4]
    apply le_trans _ (surjvalp.v_sub_ge_min_v _ _)
    apply le_min h4
    rw [mul_assoc, surjvalp.v_mul_eq_add_v, add_comm, surjvalp.v_mul_eq_add_v,
      val_of_pow_uniformizer]
    conv =>
      rhs
      rw [add_comm, add_assoc]
    rw [add_comm]
    apply add_le_add (le_of_eq rfl)
    exact le_trans h1 (le_add_right (surjvalp e.a1) _)
  have h6' : evr.valtn e1.a6 ≥ 2 * q + 1 := by
    rw [t_of_a6, evrp.factor_p_of_le_val h6, factor_p_of_le_val evrp h3, rw_a6, ←val_neg,
      sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg, neg_neg,
      pow_two]
    erw [add_assoc (-(π ^ (2 * q) * a6q2) : R)]
    rw [neg_mul_eq_mul_neg _ a6q2, factorize1 a a3q π q, ←pow_add, add_self_eq_mul_two,
      ←mul_add, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer, add_mul, ←pow_two a,
      ←one_mul (a ^ 2), add_comm (-a6q2)]
    push_cast
    exact add_le_add (le_of_eq rfl) (succ_le_of_lt (val_poly_of_double_root evrp 1 a3q (-a6q2) hdr).1)
  let t := t + u0 ^ 3 * a * (π ^ q) -- TODO use set termelab can this even do the subst?
  let a2p := sub_val evrp 1 e1.a2
  let a4pq := sub_val evrp (q + 1) e1.a4
  let a6pq2 := sub_val evrp (2 * q + 1) e1.a6
  --obvious rewriting lemmas that Lean should generate implicitly
  have rw_a2' : sub_val evrp 1 e1.a2 = a2p := rfl
  have rw_a4' : sub_val evrp (q + 1) e1.a4 = a4pq := rfl
  have rw_a6' : sub_val evrp (2 * q + 1) e1.a6 = a6pq2 := rfl
  --less obvious lemma
  have rw_a2 : sub_val evrp 1 e.a2 = a2p := by rw [←rw_a2', t_of_a2]
  if discr_2 : surjvalp (a4pq ^ 2 - 4 * a2p * a6pq2) = 0 then
    -- dbg_trace (_root_.repr π)
    -- dbg_trace (_root_.repr a2p)
    let c := if evrp.quad_roots_in_residue_field a2p a4pq a6pq2 then 4 else 2
    (m + 1, c, (r, t))
  else
  have hdr' : evrp.has_double_root a2p a4pq a6pq2 := by
    have v_a2p : surjvalp a2p = 0 := by
      rw [←rw_a2', val_sub_val_eq evrp e1.a2 1 h2']
      simp
    apply And.intro v_a2p _
    apply Enat.pos_of_ne_zero
    assumption
  let a' := evrp.double_root a2p a4pq a6pq2
  have rw_a' : evrp.double_root a2p a4pq a6pq2 = a' := rfl
  --if p = 2 then modulo a6pq2 2 else modulo (2 * a2p * -a4pq) 3
  let e2 := rst_iso (a' * π ^ q) 0 0 e1
  -- dbg_trace (_root_.repr e2)
  have h1'' : surjvalp e2.a1 ≥ 1 := by rwa [rt_of_a1]
  have h2'' : surjvalp e2.a2 = 1 := by
    rwa [r_of_a2, v_add_eq_min_v surjvalp]
    rw [h2']
    apply lt_of_succ_le
    apply val_mul_ge_of_right_ge surjvalp
    apply val_mul_ge_of_right_ge surjvalp
    rw [val_of_pow_uniformizer surjvalp]
    rw [← lt_ofN 1 q] at hq
    exact succ_le_of_lt hq
  have h3'' : surjvalp e2.a3 ≥ q + 1 := by
    rw [r_of_a3]
    apply le_trans _ (surjvalp.v_add_ge_min_v _ _)
    apply le_min h3'
    rw [mul_comm a', mul_assoc, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer]
    exact add_le_add (le_of_eq rfl) (val_mul_ge_of_right_ge surjvalp h1')
  have h4'' : surjvalp e2.a4 ≥ q + 2 := by
    rw [r_of_a4, factor_p_of_le_val evrp h4', rw_a4', factor_p_of_le_val evrp (le_of_eq h2'.symm),
      rw_a2', factorize2 a' a2p (↑π) q, ←pow_add, ←mul_add, add_comm a4pq]
    apply le_trans (le_min _ _) (surjvalp.v_add_ge_min_v _ _)
    . rw [Nat.add_succ q, Nat.succ_eq_add_one, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer]
      rw [Nat.cast_add, Nat.cast_one, add_assoc]
      rw [show (2 : ℕ∪∞) = 1 + 1 by norm_num, ← add_assoc, ← add_assoc]
      apply add_le_add (le_of_eq rfl)
      exact succ_le_of_lt (val_poly_of_double_root evrp a2p a4pq a6pq2 hdr').2
    . rw [pow_two, factorize3 a' π q, ←pow_add]
      apply val_mul_ge_of_left_ge surjvalp _
      rw [val_of_pow_uniformizer]
      exact (le_ofN _ _).2 (Nat.add_le_add (le_of_eq rfl) (Nat.succ_le_of_lt hq))
  have h6'' : surjvalp e2.a6 ≥ 2 * (q + 1) := by
    rw [r_of_a6]
    apply le_trans (le_min _ _) (surjvalp.v_add_ge_min_v _ _)
    . rw [factor_p_of_le_val evrp h6', rw_a6', factor_p_of_le_val evrp h4', rw_a4',
        factor_p_of_eq_val evrp h2', rw_a2', factorize4 a' a2p a4pq a6pq2 π q, ←pow_add, ←pow_add,
        ←pow_add, ←Nat.add_assoc, add_self_eq_mul_two q, ←mul_add, ←mul_add, mul_add,
        ←add_self_eq_mul_two 1, ←add_assoc, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer]
      push_cast
      apply add_le_add (le_of_eq rfl)
      rw [show 1 = Enat.succ 0 by rfl]
      apply succ_le_of_lt
      have := (val_poly_of_double_root evrp a2p a4pq a6pq2 hdr').1
      push_cast at this
      exact this
    . rw [mul_pow a' _ 3, ←pow_mul, mul_add, mul_one, Nat.mul_succ] -- TODO why did this break
      apply val_mul_ge_of_right_ge surjvalp
      rw [val_of_pow_uniformizer, mul_comm q]
      exact (le_ofN _ _).2 (Nat.add_le_add (le_of_eq rfl) (Nat.succ_le_of_lt hq))
  let r := r + u0 ^ 2 + a' * (π ^ q) -- TODO check these
  let t := t + u0 ^ 2 * s0 * a' * (π ^ q)
  kodaira_type_Is evrp e2 u0 r s0 t (m + 2) (q + 1) (Nat.lt_succ_of_lt hq) h1'' h2'' h3'' h4'' h6''
termination_by _ =>
  val_discr_to_nat evr.valtn e - (2 * q + 2)
decreasing_by
  simp_wf
  apply Nat.sub_lt_sub_left _ _
  . rw [← lt_ofN, ofN_val_discr_to_nat]
    exact lt_of_succ_le (v_discr_of_v_ai surjvalp e hq h1 h2 h3 h4 h6)
  . exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left q.lt_succ_self (Nat.zero_lt_succ 1)) 2


-- TODO re-add ReductionType
def tate_algorithm {R : Type u} [Repr R] [DecidableEq R] [CommRing R] [IsDomain R] {π : R}
  (evr : EnatValRing π) (e : ValidModel R) (u0 r0 s0 t0 : R) :
  Kodaira × ℕ × ℕ × (R × R × R × R) :=
  let (u, r, s, t) := (u0, r0, s0, t0)

  -- let Δ := e.discr
  let n := val_discr_to_nat evr.valtn e
  -- TODO copy these Step markrs to tateint
  -- Step 1
  if testΔ : n = 0 then (I 0, 0, 1, (u, r, s, t)) else
  have hΔ : evr.valtn e.discr ≥ 1 := by
    rw [(show ¬n = 0 ↔ 0 < n by simp [Nat.pos_iff_ne_zero]), ← lt_ofN, ofN_val_discr_to_nat] at testΔ
    exact succ_le_of_lt testΔ

  let r1s1t1 := Model.move_singular_point_to_origin_triple evr e.toModel

  let e1 := rst_triple e r1s1t1
  let (r, s) := (r + r1s1t1.fst * u ^ 2, s + u * r1s1t1.snd.fst) -- TODO urst comp
  let t := t + r1s1t1.snd.snd * u ^ 3 + s * r1s1t1.fst * u ^ 2

  -- Step 2
  if test_b2 : evr.valtn e1.b2 < 1 then -- todo change to = 0..
    let (r1, t1) := if evr.residue_char = 2 then
      (evr.norm_repr e1.a3, evr.norm_repr (e1.a3 + e1.a4))
    else
      let r1' := evr.norm_repr (-e1.b2 * e.b4)
      (r1', evr.norm_repr (e1.a1 * r1' + e1.a3))
    let e := rst_iso r1 0 t1 e1
    let r := r + r1 * u ^ 2
    let t := t + t1 * u ^ 3 + s * r1 * u ^ 2
    let c := if evr.quad_roots_in_residue_field 1 e1.a1 (-e1.a2) then n else Int.gcd 2 n
    (I n, 1, c, (u, r, s, t))
  else
  have hb2 : evr.valtn e1.b2 ≥ 1 := le_of_not_lt test_b2

  have sing_origin : Model.is_local_singular_point evr.valtn e1.toModel (0, 0) := by
    simp [rst_iso]
    apply Model.move_singular_point_to_origin
    apply Model.singular_of_val_discr
    apply lt_of_succ_le hΔ

  have h3 : evr.valtn e1.a3 ≥ 1 := by
    delta Model.is_local_singular_point at sing_origin
    have singular_dy := And.right (And.right sing_origin)
    simp [Model.dweierstrass_dy] at singular_dy
    simp only [Model.dweierstrass_dy, mul_zero, add_zero, zero_add] at singular_dy
    apply succ_le_of_lt singular_dy

  /- These two valuations can be proved at this point but are not used explicitly until stronger valuations are obtained

  have h4 : evr.valtn e1.a4 ≥ 1 := by
    delta Model.is_local_singular_point at sing_origin
    have singular_dx := And.left (And.right sing_origin)
    simp [Model.dweierstrass_dx, pow_succ, sub_eq_add_neg] at singular_dx
    apply succ_le_of_lt singular_dx

  have h6 : evr.valtn e1.a6 ≥ 1 := by
    -- TODO a6_of_is_local_singular_point_zero_zero _ _ sing_origin
    delta Model.is_local_singular_point at sing_origin
    have singular := And.left sing_origin
    simp [Model.weierstrass, pow_succ, sub_eq_add_neg] at singular
    apply succ_le_of_lt singular
    -/

  --have hb2 : evr.valtn e.b2 ≥ 1 := sorry --adapt test_b2 after change of coordinates

  -- Step 3
  if test_a6 : evr.valtn e1.a6 < 2 then (II, n, 1, (u, r, s, t)) else
  have h6 : evr.valtn e1.a6 ≥ 2 := le_of_not_lt test_a6

  -- Step 4
  if test_b8 : evr.valtn e1.b8 < 3 then (III, n-1, 2, (u, r, s, t)) else
  have hb8 : evr.valtn e1.b8 ≥ 3 := le_of_not_lt test_b8

  -- Step 5
  if test_b6 : evr.valtn e1.b6 < 3 then
    let (a3p, a6p2) := (evr.sub_val 1 e1.a3, evr.sub_val 2 e1.a6)
    let c := if evr.quad_roots_in_residue_field 1 a3p (-a6p2) then 3 else 1
    (IV, n - 2, c, (u, r, s, t))
  else
  -- Step 6
  have hb6 : evr.valtn e1.b6 ≥ 3 := le_of_not_lt test_b6

  -- have hb2 : evr.valtn e1.b2 ≥ 1 := by
  --   rw [(show e1 = rst_iso r1s1t1.fst r1s1t1.snd.fst r1s1t1.snd.snd e by rfl)]
  --   simp
  --   rw [Model.rst_b2]
  --   have : 1 ≤ evr.valtn (12 * (Model.move_singular_point_to_origin_triple evr e.toModel).fst)
  --   . simp [Model.move_singular_point_to_origin_triple, Model.singular_point_on_special]
  --     split
  --     . split
  --       . simp
  --         sorry
  --         -- rw [← Enat.succ_zero]
  --         -- apply Enat.succ_le_of_lt
  --         -- apply evr.pth_root_pos_of_pos
  --         -- simp [*]
  --       . simp
  --         sorry
  --       . simp
  --         rw [(show (1 : Enat) = 0 + (1 + 0) by simp)]
  --         repeat' apply add_le_add
  --         exact zero_le _
  --         assumption
  --         exact zero_le _
  --     . simp







    -- have : 1 ≤ evr.valtn (12 * (Model.move_singular_point_to_origin_triple evr e.toModel).fst)
    -- . simp
    --   exact le_trans this (le_add_left _ _)
    -- sorry
    -- rw [show (1 : Enat) = min 1 1 by simp]
    -- convert evr.valtn.v_add_ge_min_v _ _
    -- . exact hb2
    -- . sorry
  --   apply v_rst_b2_of_small_char evr.valtn e r1s1t1.fst r1s1t1.snd.fst r1s1t1.snd.snd hb2
  --   exact small_char_div_12 sorry evr.valtn

  --let k := if evr.valtn e.a6 < 3 then if p = 2 then 2 else evr.norm_repr e.a3 9 else 0
  have hdr_b2 : evr.has_double_root 1 e1.a1 (-e1.a2) := by
    apply And.intro (val_of_one evr.valtn) _
    apply lt_of_succ_le
    rwa [mul_one, ←neg_mul_eq_mul_neg, sub_eq_add_neg, neg_neg, pow_succ, pow_one]

  let a3p := evr.sub_val 1 e1.a3
  let a6p2 := evr.sub_val 2 e1.a6

  have hdr_b6 : evr.has_double_root 1 a3p (-a6p2) := by
    apply And.intro (val_of_one evr.valtn) _
    apply lt_of_succ_le
    rw [mul_one, ←neg_mul_eq_mul_neg, sub_eq_add_neg, neg_neg, pow_succ, pow_one]
    simp only [Model.b6] at hb6
    rw [evr.factor_p_of_le_val h3, evr.factor_p_of_le_val h6, factorize5,
        evr.valtn.v_mul_eq_add_v,
        val_of_pow_uniformizer, show (3 : ℕ∪∞) = 2 + 1 by rfl] at hb6
    exact Enat.le_of_add_le_add_left hb6

  let s1 := evr.double_root 1 e1.a1 (-e1.a2)
  let t1 := evr.double_root 1 a3p (-a6p2)

  let e2 := rst_iso 0 s1 (π * t1) e1 -- TODO change to move blah

  let t := t + t1 * u ^ 3

  have h1 : evr.valtn e2.a1 ≥ 1 := by
    rw [st_of_a1, add_comm e1.a1, ←mul_one 2]
    exact succ_le_of_lt (evr.val_poly_of_double_root 1 e1.a1 (-e1.a2) hdr_b2).2

  have h2 : evr.valtn e2.a2 ≥ 1 := by
    rw [←val_neg, st_of_a2, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg,
      neg_neg, add_comm _ (s1 ^ 2), add_comm (-e1.a2), ←add_assoc,
      ← one_mul (s1 ^ 2), mul_comm s1]
    exact succ_le_of_lt (evr.val_poly_of_double_root 1 e1.a1 (-e1.a2) hdr_b2).1

  have h3' : evr.valtn e2.a3 ≥ 2 := by
    -- rw [st_of_a1, add_comm e1.a1, ←succ_ofN, ←mul_one 2]
    -- exact succ_le_of_lt (val_poly_of_double_root hp 1 e1.a1 (-e1.a2) hdr_b2).2
    -- sorry -- = d/dt (t - pi*beta)²
    rw [st_of_a3, ←mul_assoc, mul_comm 2, add_comm e1.a3, ←mul_one 2,
      evr.factor_p_of_le_val h3, pow_one, mul_assoc, ←mul_add, evr.valtn.v_mul_eq_add_v,
      show (2 : Enat) = 1 + 1 by norm_num]
    apply add_le_add (le_of_eq evr.valtn.v_uniformizer.symm)
    exact succ_le_of_lt (evr.val_poly_of_double_root 1 a3p (-a6p2) hdr_b6).2

  have hb8 : evr.valtn e2.b8 ≥ 3 := by
    rw [st_of_b8]
    exact hb8

  have h6 : evr.valtn e2.a6 ≥ 3 := by
    rw [←val_neg, st_of_a6, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg, neg_neg,
      add_comm _ (_ ^ 2), add_comm (-e1.a6), ←add_assoc, mul_pow,
      evr.factor_p_of_le_val h3, evr.factor_p_of_le_val h6, neg_mul_eq_mul_neg (_ : R) (evr.sub_val 2 e1.toModel.a6), factorize6,
      evr.valtn.v_mul_eq_add_v, show (3 : ℕ∪∞) = 2 + 1 by rfl]
    apply add_le_add (le_of_eq (val_of_pow_uniformizer evr.valtn).symm)
    exact succ_le_of_lt (evr.val_poly_of_double_root 1 a3p (-a6p2) hdr_b6).1

  have h4 : evr.valtn e2.a4 ≥ 2 := by -- using pi³|b_8
    have h4' : evr.valtn (e2.a4 ^ 2) ≥ 3 := by
      rw [←add_zero (e2.a4 ^ 2), ←add_neg_self e2.b8, ←add_assoc, add_comm (_ ^ 2)]
      delta Model.b8
      rw [sub_eq_add_neg, add_assoc _ _ (_ ^ 2), add_comm _ (_ ^ 2), pow_two,
        add_neg_self, add_zero, ←sub_eq_add_neg _ (_ * _),
        show e2.a1 * e2.a1 * e2.a6 - e2.a1 * e2.a3 * e2.a4 +
          4 * e2.a2 * e2.a6 + e2.a2 * e2.a3 * e2.a3 - e2.a4 * e2.a4 = e2.b8 by rfl, sub_eq_add_neg,
          neg_mul_eq_mul_neg, evr.factor_p_of_le_val hb8, evr.factor_p_of_le_val h1,
          evr.factor_p_of_le_val h3', evr.factor_p_of_le_val h6, neg_mul_eq_mul_neg, factorize9]
      apply val_mul_ge_of_left_ge evr.valtn
      exact le_of_eq (val_of_pow_uniformizer evr.valtn).symm
    cases le_or_lt (evr.valtn e2.a4) 1 with
    | inl v_a4_le_1 =>
      apply False.elim
      rw [pow_two, evr.valtn.v_mul_eq_add_v] at h4'
      have x := le_trans h4' (add_le_add v_a4_le_1 v_a4_le_1)
      simp at x
      -- simpa using
    | inr v_a4_gt_1 =>
      exact succ_le_of_lt v_a4_gt_1

  let (a2p, a4p2, a6p3) := (evr.sub_val 1 e2.a2, evr.sub_val 2 e2.a4, evr.sub_val 3 e2.a6)
  -- 18bcd – 4b³d + b²c² – 4c³ – 27d²
  let Δcube := -4 * a2p^3 * a6p3 + a2p^2 * a4p2^2 - 4 * a4p2^3 - 27 * a6p3^2

  if test_Δcubic : evr.valtn (Δcubic (model_to_cubic evr e2)) = 0 then -- TODO don't recompute a2p,a4pw above
    let c := 1 + evr.count_roots_cubic 1 a2p a4p2 a6p3
    (Is 0, n - 4, c, (u, r, s, t))
  else
  -- Step 7
  if test_δcubic : evr.valtn (δmultiplicity (model_to_cubic evr e2)) = 0 then
  -- if evr.valtn (3 * a4p2 - a2p ^ 2) = 0 then
    let r1 := π * (evr.norm_repr (if evr.residue_char = 2 then a4p2 else a2p * a4p2)) -- TODO wrong
    have e2_cubic_has_double_root : cubic_has_double_root evr e2 :=
      And.intro (Enat.pos_of_ne_zero test_Δcubic) test_δcubic
    let e3 := move_cubic_double_root_to_origin_iso evr e2
    let r := r + u^2 * r1
    let t := t + u ^ 2 * s * r1
    have h1' : evr.valtn e3.a1 ≥ 1 := by
      simp only [move_cubic_double_root_to_origin_iso]
      rwa [rt_of_a1]

    have h2' : evr.valtn e3.a2 = 1 := by
      have h2'' : evr.valtn e3.a2 ≥ 1 := by
        simp only [move_cubic_double_root_to_origin_iso]
        rw [r_of_a2, evr.factor_p_of_le_val h2, pow_one, ←mul_assoc, mul_comm 3, mul_assoc, ←mul_add]
        apply val_mul_ge_of_left_ge
        exact le_of_eq evr.valtn.v_uniformizer.symm
      rw [evr.factor_p_of_le_val h2'', evr.valtn.v_mul_eq_add_v, pow_one, evr.valtn.v_uniformizer,
        (move_cubic_double_root_to_origin evr e2 e2_cubic_has_double_root).1, add_zero]

    have h3 : evr.valtn e3.a3 ≥ 2 := by
      simp only [move_cubic_double_root_to_origin_iso, r_of_a3]
      apply val_add_ge_of_ge _ h3'
      rw [mul_assoc, evr.factor_p_of_le_val h1, mul_comm _ (_ ^ 1 * _), ←mul_assoc, ←mul_assoc,
        mul_comm _ (_ ^ 1), ←pow_succ', mul_assoc]
      apply val_mul_ge_of_left_ge
      rw [val_of_pow_uniformizer evr.valtn]
      exact le_refl _

    have h4' : evr.valtn e3.a4 ≥ 3 := by
      have h4'' : evr.valtn e3.a4 ≥ 2 := by
        simp only [move_cubic_double_root_to_origin_iso]
        rw [r_of_a4, evr.factor_p_of_le_val h4, evr.factor_p_of_le_val h2, factorize7]
        apply val_mul_ge_of_left_ge evr.valtn _
        exact le_of_eq (val_of_pow_uniformizer evr.valtn).symm
      rw [evr.factor_p_of_le_val h4'', evr.valtn.v_mul_eq_add_v, show (3 : ℕ∪∞) = 2 + 1 by rfl]
      apply add_le_add
      . exact le_of_eq (val_of_pow_uniformizer evr.valtn).symm
      . exact succ_le_of_lt (move_cubic_double_root_to_origin evr e2 e2_cubic_has_double_root).2.1

    have h6 : evr.valtn e3.a6 ≥ 4 := by
      have h6' : evr.valtn e3.a6 ≥ 3 := by
        simp only [move_cubic_double_root_to_origin_iso]
        rw [r_of_a6, evr.factor_p_of_le_val h6, evr.factor_p_of_le_val h4, evr.factor_p_of_le_val h2, factorize8]
        apply val_mul_ge_of_left_ge evr.valtn _
        exact le_of_eq (val_of_pow_uniformizer evr.valtn).symm
      rw [evr.factor_p_of_le_val h6', evr.valtn.v_mul_eq_add_v, show (4 : ℕ∪∞) = 3 + 1 by rfl]
      apply add_le_add
      . exact le_of_eq (val_of_pow_uniformizer evr.valtn).symm
      . exact succ_le_of_lt (move_cubic_double_root_to_origin evr e2 e2_cubic_has_double_root).2.2

    -- Step 7 (subprocedure)
    let (m, c, (r, t)) := kodaira_type_Is evr e3 u r s t 1 2 (Nat.lt_succ_self 1) h1' h2' h3 h4' h6
    -- let (m, c, (r, t)) := (0,0,0,0) --sorry--kodaira_type_Is p hp e u r s t 1 2 (Nat.lt_succ_self 1) h1 h2 h3 h4 h6
    (Is m, n - m - 4, c, (u, r, s, t))
  else

  have e2_cubic_has_triple_root : cubic_has_triple_root evr e2 :=
    And.intro (Enat.pos_of_ne_zero test_Δcubic) (Enat.pos_of_ne_zero test_δcubic)

  let e3 := move_cubic_triple_root_to_origin_iso evr e2
  -- let r1 := π * (evr.norm_repr (if evr.residue_char == 2 then -a2p else -a6p3))
  -- let e := rst_iso r1 0 0 e
  -- let r := r + u ^ 2 * r1
  -- let t := t + u ^ 2 * s * r1
  have He3 : move_cubic_triple_root_to_origin_iso evr e2 = e3 := by rfl

  have h2' : evr.valtn e3.a2 ≥ 2 := by-- T=0 triple root => a_2,1 = 0
    have h2'' : evr.valtn e3.a2 ≥ 1 := by
      --erw [←Enat.succ_zero, ← Enat.lt_iff_succ_le]
      have := move_cubic_triple_root_to_origin evr e2 e2_cubic_has_triple_root
      -- sorry
      simp only [move_cubic_triple_root_to_origin_iso]
      -- rw [r_of_a2, evr.factor_p_of_le_val h2, pow_one, ←mul_assoc, mul_comm 3, mul_assoc, ←mul_add]
      -- apply val_mul_ge_of_left_ge
      -- exact le_of_eq evr.valtn.v_uniformizer.symm
      sorry
    rw [evr.factor_p_of_le_val h2'', evr.valtn.v_mul_eq_add_v, pow_one, show (2 : ℕ∪∞) = 1 + 1 by rfl]
    apply add_le_add
    . exact le_of_eq evr.valtn.v_uniformizer.symm
    . exact succ_le_of_lt (move_cubic_triple_root_to_origin evr e2 e2_cubic_has_triple_root).1

  have h3 : evr.valtn e3.a3 ≥ 2 := by
    simp only [move_cubic_triple_root_to_origin_iso]
    rw [r_of_a3, evr.factor_p_of_le_val h1, pow_one]
    apply val_add_ge_of_ge evr.valtn
    . exact h3'
    . sorry
      -- rw [←mul_assoc, mul_comm _ (π : R), ←mul_assoc, ←pow_two, mul_assoc]
      -- apply val_mul_ge_of_left_ge evr.valtn (le_of_eq (val_of_pow_uniformizer evr.valtn).symm)

  have h6 : evr.valtn e3.a6 ≥ 4 := by-- T=0 triple root => a_6,3 = 0
    have h6' : evr.valtn e3.a6 ≥ 3 := by
      simp only [move_cubic_triple_root_to_origin_iso]
      sorry
      -- rw [r_of_a6, evr.factor_p_of_le_val h6, evr.factor_p_of_le_val h4,
      --   evr.factor_p_of_le_val h2, factorize8]
      -- apply val_mul_ge_of_left_ge evr.valtn _
      -- exact le_of_eq (val_of_pow_uniformizer evr.valtn).symm
    rw [evr.factor_p_of_le_val h6', evr.valtn.v_mul_eq_add_v, show (4 : ℕ∪∞) = 3 + 1 by rfl]
    apply add_le_add
    . exact le_of_eq (val_of_pow_uniformizer evr.valtn).symm
    . exact succ_le_of_lt (move_cubic_triple_root_to_origin evr e2 e2_cubic_has_triple_root).2.2

  -- have h2 : evr.valtn e3.a2 ≥ 2 := sorry
  -- have h3 : evr.valtn e3.a3 ≥ 2 := sorry
  -- --have h4 : evr.valtn e.a4 ≥ 3 := sorry
  -- have h6 : evr.valtn e3.a6 ≥ 4 := sorry

  let a3p2 := evr.sub_val 2 e3.a3
  let a6p4 := evr.sub_val 4 e3.a6
  -- Step 8
  if discr_b6p4 : evr.valtn (a3p2 ^ 2 + 4 * a6p4) = 0 then
    let c := if evr.quad_roots_in_residue_field 1 a3p2 (-a6p4) then 3 else 1
    (IVs, n - 6, c, (u, r, s, t))
  else

  have h_b6p4 : evr.has_double_root 1 a3p2 (-a6p4) := by -- this should be a lemma
    -- refine And.intro (val_of_one evr.valtn) (Enat.pos_of_ne_zero (by simpa))
    sorry

  -- let a := if evr.residue_char = 2 then evr.norm_repr a6p4 else evr.norm_repr (2 * a3p2)
  let a := evr.double_root 1 a3p2 (-a6p4)
  have Ha : evr.double_root 1 (evr.sub_val 2 e3.a3) (-evr.sub_val 4 e3.a6) = a := by rfl
  let k := a * (π ^ 2 : R)
  let e4 := rst_iso 0 0 k e3
  have He4 : rst_iso 0 0 (a * (π : R) ^ 2) e3 = e4 := by rfl
  let t := t + k * u ^ 3
  --have h6 : evr.valtn e.a6 ≥ 5 := sorry
  have h3 : evr.valtn e4.a3 ≥ 3 := by
    rw [t_of_a3, ←mul_one 2, evr.factor_p_of_le_val h3, ←mul_assoc (2*1), mul_comm ((2*1) * _),
      ←mul_add, add_comm, show (3 : ℕ∪∞) = 2 + 1 by rfl, evr.valtn.v_mul_eq_add_v]
    apply add_le_add
    . exact le_of_eq (val_of_pow_uniformizer evr.valtn).symm
    . exact succ_le_of_lt (evr.val_poly_of_double_root 1 a3p2 (-a6p4) h_b6p4).2



  -- Step 9
  if test_a4 : evr.valtn e4.a4 < 4 then (IIIs, n - 7, 2, (u, r, s, t)) else
  have h4 : evr.valtn e4.a4 ≥ 4 := le_of_not_lt test_a4

  -- Step 10
  if test_a6 : evr.valtn e4.a6 < 6 then (IIs, n - 8, 1, (u, r, s, t)) else
  have h6 : evr.valtn e4.a6 ≥ 6 := le_of_not_lt test_a6

  have h1 : evr.valtn e4.a1 ≥ 1 := by
    rw [rt_of_a1]
    simp only [move_cubic_triple_root_to_origin_iso]
    rw [rt_of_a1]
    exact h1

  have h2 : evr.valtn e4.a2 ≥ 2 := by
    rw [t_of_a2]
    exact h2'

  -- Step 11
  tate_algorithm evr (ValidModel.pi_scaling evr e4 h1 h2 h3 h4 h6) (π * u) r s t
termination_by _ =>
  val_discr_to_nat evr.valtn e
decreasing_by
  simp (config := {zeta := false})
    [invImage, InvImage, Prod.lex, sizeOfWFRel,
          measure, Nat.lt_wfRel, WellFoundedRelation.rel]
  -- rw [He3, Ha]

  -- rw [He4]
  rw [pi_scaling_val_discr_to_nat evr e4 h1 h2 h3 h4 h6]
  have discr_eq : val_discr_to_nat evr.valtn e4 = val_discr_to_nat evr.valtn e := by
    rw [iso_rst_val_discr_to_nat]
    simp only [move_cubic_triple_root_to_origin_iso]
    rw [iso_rst_val_discr_to_nat, iso_rst_val_discr_to_nat]
    simp only [rst_triple]
    rw [iso_rst_val_discr_to_nat]
  rw [discr_eq]
  apply Nat.sub_lt_of_pos_le (Nat.zero_lt_succ 11)
  rw [←le_ofN, ←discr_eq, ofN_val_discr_to_nat, show Nat.succ 11 = 12 by rfl]

  exact Model.val_discr_of_val_ai evr e4.toModel h1 h2 h3 h4 h6

-- def test_model : ValidModel ℤ := ⟨⟨1, -1, 1, -23130, -1322503⟩, by simp⟩
def test_model : ValidModel ℤ := ⟨⟨1,-1,1,-965,-13940⟩, by simp⟩

#eval tate_algorithm (Int.primeEVR ((by sorry) : Nat.Prime 7)) test_model 1 0 0 0
