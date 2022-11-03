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
section ring_lemmas

variable {R : Type u} [IntegralDomain R]

lemma factorize1 (root b p : R) (q : ℕ) : root * p ^ q * (p ^ q * b) + root * p ^ q * (root * p ^ q) = p ^ q * p ^ q * ((root + b) * root) := by ring

lemma factorize2 (root a p : R) (q : ℕ) : 2 * (root * p ^ q) * (p ^ 1 * a) = p ^ q  * p ^ 1  * (2 * a * root) := by ring

lemma factorize3 (root p : R) (q : ℕ) : 3 * (root * p ^ q * (root * p ^ q)) = p ^ q * p ^ q * (3 * root * root) := by ring

lemma factorize4 (root a b c p : R) (q : ℕ) : p ^ (2 * q + 1) * c + root * p ^ q * (p ^ (q + 1) * b) + (root * p ^ q) ^ 2 * (p ^ 1 * a) = p ^ q * p ^ q * p ^ 1 * (a * root ^ 2) + p ^ q * p ^ (q + 1) * (b * root) + p ^ (2 * q + 1) * c := by ring

lemma factorize5 (b c p : R) : p ^ 1 * b * (p ^ 1 * b) + 4 * (p ^ 2 * c) = p ^ 2 * (b * b + 4 * c) := by ring

end ring_lemmas

-- unsafe
-- def tate_algorithm {R : Type u} [IntegralDomain R] {pi : R} (evr : EnatValRing pi)
--   (e : ValidModel R) (u0 r0 s0 t0 : R) : Kodaira × ℕ × ℕ × (R × R × R × R) :=
--   let (u, r, s, t) := (u0, r0, s0, t0)

--   let Δ := e.discr
--   let n := val_discr_to_nat evr.valtn e
--   if testΔ : n = 0 then (I 0, 0, 1, (u, r, s, t)) else
--   have hΔ : evr.valtn.v e.discr ≥ ofN 1 := by
--     rw [(show ¬n = 0 ↔ 0 < n by simp [Nat.pos_iff_ne_zero]), lt_ofN, ofN_val_discr_to_nat] at testΔ
--     exact succ_le_of_lt testΔ

--   if test_b2 : evr.valtn.v e.b2 < ofN 1 then
--     let (r1, t1) := if evr.residue_char = 2 then
--       (evr.norm_repr e.a3, evr.norm_repr (e.a3 + e.a4))
--     else
--       let r1' := evr.norm_repr (-e.b2 * e.b4)
--       (r1', evr.norm_repr (e.a1 * r1' + e.a3))
--     let e := rst_iso r1 0 t1 e
--     let r := r + r1 * u ^ 2
--     let t := t + t1 * u ^ 3 + s * r1 * u ^ 2
--     let c := if evr.quad_roots_in_residue_field 1 e.a1 (-e.a2) then n else Int.gcd 2 n
--     (I n, 1, c, (u, r, s, t))
--   else
--   have hb2 : evr.valtn.v e.b2 ≥ ofN 1 := le_of_not_lt test_b2

--   let r1s1t1 := Model.move_singular_point_to_origin_triple evr e.toModel

--   let e' := rst_triple e r1s1t1
--   let (r, s) := (r + r1s1t1.fst * u ^ 2, s + u * r1s1t1.snd.fst)
--   let t := t + r1s1t1.snd.snd * u ^ 3 + s * r1s1t1.fst * u ^ 2

--   have sing_origin : Model.is_local_singular_point evr.valtn e'.toModel (0, 0) := by
--     simp [rst_iso]
--     apply Model.move_singular_point_to_origin
--     apply Model.singular_of_val_discr
--     apply lt_of_succ_le hΔ

--   have h3 : evr.valtn.v e'.a3 ≥ ofN 1 := by
--     delta Model.is_local_singular_point at sing_origin
--     have singular_dy := And.right (And.right sing_origin)
--     simp [Model.dweierstrass_dy] at singular_dy
--     rw [<-succ_ofN]
--     apply succ_le_of_lt singular_dy

--   have h4 : evr.valtn.v e'.a4 ≥ ofN 1 := by
--     delta Model.is_local_singular_point at sing_origin
--     have singular_dx := And.left (And.right sing_origin)
--     simp [Model.dweierstrass_dx, pow_succ, sub_eq_add_neg] at singular_dx
--     rw [<-succ_ofN]
--     apply succ_le_of_lt singular_dx

--   have h6 : evr.valtn.v e'.a6 ≥ ofN 1 := by
--     delta Model.is_local_singular_point at sing_origin
--     have singular := And.left sing_origin
--     simp [Model.weierstrass, pow_succ, sub_eq_add_neg] at singular
--     rw [<-succ_ofN]
--     apply succ_le_of_lt singular

--   --have hb2 : evr.valtn.v e.b2 ≥ ofN 1 := sorry --adapt test_b2 after change of coordinates

--   if test_a6 : evr.valtn.v e'.a6 < ofN 2 then (II, n, 1, (u, r, s, t)) else
--   have h6 : evr.valtn.v e'.a6 ≥ ofN 2 := le_of_not_lt test_a6

--   if test_b8 : evr.valtn.v e'.b8 < ofN 3 then (III, n-1, 2, (u, r, s, t)) else
--   have hb8 : evr.valtn.v e'.b8 ≥ ofN 3 := le_of_not_lt test_b8

--   if test_b6 : evr.valtn.v e'.b6 < ofN 3 then
--     let (a3p, a6p2) := (evr.sub_val e'.a3 1, evr.sub_val e'.a6 2)
--     let c := if evr.quad_roots_in_residue_field 1 a3p (-a6p2) then 3 else 1
--     (IV, n - 2, c, (u, r, s, t))
--   else
--   have hb6 : evr.valtn.v e'.b6 ≥ ofN 3 := le_of_not_lt test_b6

--   have hb2 : evr.valtn.v e'.b2 ≥ ofN 1 := by
--     rw [(show e' = rst_iso r1s1t1.fst r1s1t1.snd.fst r1s1t1.snd.snd e by rfl)]
--     apply v_rst_b2_of_small_char evr.valtn e r1s1t1.fst r1s1t1.snd.fst r1s1t1.snd.snd hb2
--     exact small_char_div_12 p_is_2_or_3 evr.valtn

--   --let k := if evr.valtn.v e.a6 < ofN 3 then if p = 2 then 2 else evr.norm_repr e.a3 9 else 0
--   have hdr_b2 : evr.has_double_root 1 e'.a1 (-e'.a2) := by
--     apply And.intro (val_of_one evr.valtn) _
--     apply lt_of_succ_le
--     rw [mul_one, ←neg_mul_right, sub_eq_add_neg, neg_neg (4 * e'.toModel.a2), succ_ofN, pow_succ, pow_one]
--     assumption

--   let a3p := evr.sub_val e'.a3 1
--   let a6p2 := evr.sub_val e'.a6 2

--   have hdr_b6 : evr.has_double_root 1 a3p (-a6p2) := by
--     apply And.intro (val_of_one evr.valtn) _
--     apply lt_of_succ_le
--     rw [mul_one, ←neg_mul_right, sub_eq_add_neg, neg_neg (4 * a6p2), succ_ofN, pow_succ, pow_one]
--     simp only [Model.b6] at hb6
--     rw [evr.factor_p_of_le_val h3, evr.factor_p_of_le_val h6, factorize5, evr.valtn.v_mul_eq_add_v, val_of_pow_uniformizer, (show 3 = 2 + 1 by rfl), ←add_ofN] at hb6
--     exact Enat.le_of_add_le_add_left hb6

--   let s1 := double_root 1 e'.a1 (-e'.a2) p
--   let t1 := double_root 1 e'.a3 (-e'.a6) p

--   let e'' := rst_iso 0 s1 (p * t1) e'

--   let t := t + t1 * u ^ 3

--   have h1 : evr.valtn.v e''.a1 ≥ ofN 1 := by
--     rw [st_of_a1, add_comm e'.a1, ←succ_ofN, ←mul_one 2]
--     exact succ_le_of_lt (val_poly_of_double_root hp 1 e'.a1 (-e'.a2) hdr_b2).2

--   have h2 : evr.valtn.v e''.a2 ≥ ofN 1 := by
--     rw [←val_neg, st_of_a2, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg, neg_neg, Int.add_comm _ (s1 ^ 2), Int.add_comm (-e'.a2), ←Int.add_assoc, ←succ_ofN, ←one_mul (s1 ^ 2), mul_comm s1]
--     exact succ_le_of_lt (val_poly_of_double_root hp 1 e'.a1 (-e'.a2) hdr_b2).1

--   have h3 : evr.valtn.v e''.a3 ≥ ofN 2 := by
--     rw [st_of_a1, add_comm e'.a1, ←succ_ofN, ←mul_one 2]
--     exact succ_le_of_lt (val_poly_of_double_root hp 1 e'.a1 (-e'.a2) hdr_b2).2
--     sorry -- = d/dt (t - pi*beta)²
--   have h4 : evr.valtn.v e''.a4 ≥ ofN 2 := sorry -- using pi³|b_8
--   have h6 : evr.valtn.v e''.a6 ≥ ofN 3 := sorry -- = -(t - pi*beta)²

--   let (a2p, a4p2, a6p3) := (sub_val evrp e.a2 1, sub_val evrp e.a4 2, sub_val evrp e.a6 3)
--   -- 18bcd – 4b³d + b²c² – 4c³ – 27d²
--   let Δcube := -4 * a2p^3 * a6p3 + a2p^2 * a4p2^2 - 4 * a4p2^3 - 27 * a6p3^2
--   if evr.valtn.v Δcube = 0 then
--     let c := 1 + count_roots_cubic 1 a2p a4p2 a6p3 p
--     (Is 0, n - 4, c, (u, r, s, t))
--   else
--   if evr.valtn.v (3 * a4p2 - a2p ^ 2) = 0 then
--     let r1 := p * (evr.norm_repr (if p = 2 then a4p2 else a2p * a4p2) p)
--     let e := rst_iso r1 0 0 e
--     let r := r + u^2 * r1
--     let t := t + u ^ 2 * s * r1
--     have h1 : evr.valtn.v e.a1 ≥ ofN 1 := sorry -- preserved
--     have h2 : evr.valtn.v e.a2 = ofN 1 := sorry -- T=0 double root => a_2,1 /= 0
--     have h3 : evr.valtn.v e.a3 ≥ ofN 2 := sorry -- preserved
--     have h4 : evr.valtn.v e.a4 ≥ ofN 3 := sorry -- T=0 double root => a_4,2 = 0
--     have h6 : evr.valtn.v e.a6 ≥ ofN 4 := sorry -- T=0 double root => a_6,3 = 0
--     let (m, c, (r, t)) := kodaira_type_Is p hp e u r s t 1 2 (Nat.lt_succ_self 1) h1 h2 h3 h4 h6
--     (Is m, n - m - 4, c, (u, r, s, t))
--   else

--   let r1 := p * (evr.norm_repr (if p = 2 then -a2p else -a6p3) p)
--   let e := rst_iso r1 0 0 e
--   let r := r + u ^ 2 * r1
--   let t := t + u ^ 2 * s * r1
--   have h2 : evr.valtn.v e.a2 ≥ ofN 2 := sorry -- T=0 triple root => a_2,1 = 0
--   have h3 : evr.valtn.v e.a3 ≥ ofN 2 := sorry -- preserved
--   --have h4 : evr.valtn.v e.a4 ≥ ofN 3 := sorry
--   have h6 : evr.valtn.v e.a6 ≥ ofN 4 := sorry -- T=0 triple root => a_6,3 = 0

--   let (a3p2, a6p4) := (sub_val evrp e.a3 2, sub_val evrp e.a6 4)
--   if evr.valtn.v (a3p2 ^ 2 + 4 * a6p4) = 0 then
--     let c := if quad_root_in_ZpZ 1 a3p2 (-a6p4) p then 3 else 1
--     (IVs, n - 6, c, (u, r, s, t))
--   else
--   let a := if p = 2 then evr.norm_repr a6p4 else evr.norm_repr (2 * a3p2)
--   let k := -a * (p ^ 2 : ℕ)
--   let e := rst_iso 0 0 k e
--   let t := t + k * u ^ 3
--   have h3 : evr.valtn.v e.a3 ≥ ofN 3 := sorry --change of coord using root
--   --have h6 : evr.valtn.v e.a6 ≥ ofN 5 := sorry

--   if test_a4 : evr.valtn.v e.a4 < ofN 4 then (IIIs, n - 7, 2, (u, r, s, t)) else
--   have h4 : evr.valtn.v e.a4 ≥ ofN 4 := le_of_not_lt test_a4

--   if test_a6 : evr.valtn.v e.a6 < ofN 6 then (IIs, n - 8, 1, (u, r, s, t)) else
--   have h6 : evr.valtn.v e.a6 ≥ ofN 6 := le_of_not_lt test_a6

--   have h1 : evr.valtn.v e.a1 ≥ ofN 1 := sorry --preserved
--   have h2 : evr.valtn.v e.a2 ≥ ofN 2 := sorry --preserved
--   tate_small_prime p hp (u_iso (p : ℤ) e) (p * u) r s t
