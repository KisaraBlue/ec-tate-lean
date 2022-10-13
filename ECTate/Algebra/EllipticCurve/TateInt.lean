import ECTate.Algebra.EllipticCurve.Kronecker
import ECTate.Algebra.EllipticCurve.Model
import ECTate.Algebra.EllipticCurve.ValuedRing
import ECTate.Data.Nat.Enat
import Mathlib.Init.Data.Int.Basic
import Mathlib.Tactic.LibrarySearch
import ECTate.Algebra.EllipticCurve.LocalEC
import Mathlib.Init.Algebra.Order


lemma nat_cast_pow (p q : Nat) : ((p ^ q : ℕ) : ℤ) = (p : ℤ) ^ q := by simp
lemma nat_cast_pow_one (p : Nat) : (↑p) ^ 1 = ↑p := by simp




open Enat
open EnatValRing

inductive Kodaira where
  | I     : Nat → Kodaira --for both I0 and In with n > 0
  | II    : Kodaira
  | III   : Kodaira
  | IV    : Kodaira
  | Is    : Nat → Kodaira
  | IIs   : Kodaira
  | IIIs  : Kodaira
  | IVs   : Kodaira
deriving DecidableEq

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


section ring_lemmas

variable {R : Type u} [IntegralDomain R]

lemma factorize1 (root b p : R) (q : ℕ) : root * p ^ q * (p ^ q * b) + root * p ^ q * (root * p ^ q) = p ^ q * p ^ q * ((root + b) * root) := by ring

lemma factorize2 (root a p : R) (q : ℕ) : 2 * (root * p ^ q) * (p ^ 1 * a) = p ^ q  * p ^ 1  * (2 * a * root) := by ring

lemma factorize3 (root p : R) (q : ℕ) : 3 * (root * p ^ q * (root * p ^ q)) = p ^ q * p ^ q * (3 * root * root) := by ring

lemma factorize4 (root a b c p : R) (q : ℕ) : p ^ (2 * q + 1) * c + root * p ^ q * (p ^ (q + 1) * b) + (root * p ^ q) ^ 2 * (p ^ 1 * a) = p ^ q * p ^ q * p ^ 1 * (a * root ^ 2) + p ^ q * p ^ (q + 1) * (b * root) + p ^ (2 * q + 1) * c := by ring

lemma factorize5 (b c p : R) : p ^ 1 * b * (p ^ 1 * b) + 4 * (p ^ 2 * c) = p ^ 2 * (b * b + 4 * c) := by ring

lemma factorize6 (p x b c) : p ^ 2 * x ^ 2 + p * x * (p ^ 1 * b) + p ^ 2 * -c = p ^ 2 * (1 * x ^ 2 + b * x + -c) := by ring

lemma factorize7 (a b r p : R) : p ^ 2 * a + 2 * (p * r) * (p ^ 1 * b) + 3 * (p * r) ^ 2 = p ^ 2 * (a + 2 * r * b + 3 * r ^ 2) := by ring

lemma factorize8 (a b c r p : R) : (p ^ 3 * a) + (p * r) * (p ^ 2 * b) + (p * r) ^ 2 * (p ^ 1 * c) + (p * r) ^ 3 = p ^ 3 * (a + r * b + r ^ 2 * c + r ^ 3) := by ring

lemma factorize9 (a1 a2 a3 a4 a6 b8 p : R) : p ^ 1 * a1 * (p ^ 1 * a1) * (p ^ 3 * a6) + p ^ 1 * a1 * (p ^ 2 * a3) * -a4 + 4 * a2 * (p ^ 3 * a6) + a2 * (p ^ 2 * a3) * (p ^ 2 * a3) + p ^ 3 * -b8 = p ^ 3 * (p ^ 1 * a1 * (p ^ 1 * a1) * a6 + a1 * a3 * -a4 + 4 * a2 * a6 + a2 * a3 * (p ^ 1 * a3) + -b8) := by ring

end ring_lemmas


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
  let n := val_discr_to_nat navp e
  let ⟨vpj, k, integralInv⟩ : ℤ × ℕ × Bool := --'metavariables' kernel error if type not provided
    match (primeEVR hp).valtn.v (c4 ^ 3) with
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
        natAbs (3 + kronecker (if ν % 2 = 1 then (Δ * c6 / (p ^ (ν + 9) : ℕ)) else (Δ / (p ^ (ν + 6) : ℕ))) p),
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



--syntax (name := simpRST) "simp_rst" : tactic := simp only [rst_iso, Model.rst_iso, Model.iso]


def kodaira_type_Is (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) (u0 r0 s0 t0 : ℤ) (m q : ℕ)
  (hq : 1 < q) (h1 : (primeEVR hp).valtn.v e.a1 ≥ ofN 1) (h2 : (primeEVR hp).valtn.v e.a2 = ofN 1) (h3 : (primeEVR hp).valtn.v e.a3 ≥ ofN q) (h4 : (primeEVR hp).valtn.v e.a4 ≥ ofN (q + 1)) (h6 : (primeEVR hp).valtn.v e.a6 ≥ ofN (2 * q)) : ℕ × ℕ × ℤ × ℤ :=
  let evrp := primeEVR hp
  let surjvalp := evrp.valtn
  let (r, t) := (r0, t0)
  let a3q := sub_val evrp e.a3 q
  let a6q2 := sub_val evrp e.a6 (2 * q)
  --obvious rewriting lemmas that Lean should generate implicitely
  have rw_a6 : sub_val evrp e.a6 (2 * q) = a6q2 := rfl

  if discr_1 : surjvalp.v (a3q ^ 2 + 4 * a6q2) = 0 then
    let c := if quad_root_in_ZpZ 1 a3q (-a6q2) p then 4 else 2
    (m, c, (r, t))
  else
  have hdr : has_double_root 1 a3q (-a6q2) hp := by
    apply And.intro (val_of_one surjvalp) _
    apply pos_of_ne_zero
    rw [mul_one, ←neg_mul_right, sub_eq_add_neg, neg_neg]
    exact discr_1
  let a := double_root 1 a3q (-a6q2) p
  let rw_a : double_root 1 a3q (-a6q2) p = a := rfl
  --if p = 2 then modulo a6q2 2 else modulo (2 * -a3q) 3
  let e1 := rst_iso 0 0 (a * (p ^ q : ℕ)) e
  have h1' : surjvalp.v e1.a1 ≥ ofN 1 := by
    rw [rt_of_a1]
    assumption
  have h2' : surjvalp.v e1.a2 = ofN 1 := by
    rw [t_of_a2]
    assumption
  have h3' : surjvalp.v e1.a3 ≥ ofN (q+1) := by
    rw [t_of_a3, factor_p_of_le_val evrp h3, ←mul_assoc, mul_comm (2*a), nat_cast_pow, ←mul_add, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer, ←add_ofN]
    apply add_le_add (le_of_eq rfl)
    rw [←succ_ofN, Int.add_comm, ←mul_one 2]
    exact succ_le_of_lt (val_poly_of_double_root hp 1 a3q (-a6q2) hdr).2
  have h4' : surjvalp.v e1.a4 ≥ ofN (q+1) := by
    rw [t_of_a4]
    apply Enat.le_trans _ (surjvalp.v_add_ge_min_v _ _)
    apply le_min h4
    rw [mul_assoc, val_of_neg, surjvalp.v_mul_eq_add_v, Enat.add_comm, surjvalp.v_mul_eq_add_v, nat_cast_pow, val_of_pow_uniformizer, ←add_ofN]
    apply Enat.le_trans _ (le_add_right (ofN q + surjvalp.v e.a1) _)
    exact add_le_add (le_of_eq rfl) h1
  have h6' : (primeEVR hp).valtn.v e1.a6 ≥ ofN (2 * q + 1) := by
    rw [t_of_a6, factor_p_of_le_val evrp h6, factor_p_of_le_val evrp h3, rw_a6, ←val_of_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg, neg_neg, neg_mul_right, nat_cast_pow, pow_two, Int.add_assoc, factorize1 a a3q (↑p) q, ←pow_add, add_self_eq_mul_two, ←mul_add, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer, ←add_ofN, add_mul, ←pow_two, ←one_mul (a ^ 2), Int.add_comm]
    exact add_le_add (le_of_eq rfl) (succ_le_of_lt (val_poly_of_double_root hp 1 a3q (-a6q2) hdr).1)
  let t := t + u0 ^ 3 * a * (p ^ q : ℕ)
  let a2p := sub_val evrp e1.a2 1
  let a4pq := sub_val evrp e1.a4 (q + 1)
  let a6pq2 := sub_val evrp e1.a6 (2 * q + 1)
  --obvious rewriting lemmas that Lean should generate implicitely
  have rw_a2' : sub_val evrp e1.a2 1 = a2p := rfl
  have rw_a4' : sub_val evrp e1.a4 (q + 1) = a4pq := rfl
  have rw_a6' : sub_val evrp e1.a6 (2 * q + 1) = a6pq2 := rfl
  --less obvious lemma
  have rw_a2 : sub_val evrp e.a2 1 = a2p := by
    rw [←rw_a2', t_of_a2]
  if discr_2 : surjvalp.v (a4pq ^ 2 - 4 * a2p * a6pq2) = 0 then
    let c := if quad_root_in_ZpZ a2p a4pq a6pq2 p then 4 else 2
    (m + 1, c, (r, t))
  else
  have hdr' : has_double_root a2p a4pq a6pq2 hp := by
    have v_a2p : surjvalp.v a2p = 0 := by
      rw [←rw_a2', val_sub_val_eq evrp e1.a2 1 h2']
      simp
    apply And.intro v_a2p _
    apply pos_of_ne_zero
    assumption
  let a' := double_root a2p a4pq a6pq2 p
  have rw_a' : double_root a2p a4pq a6pq2 p = a' := rfl
  --if p = 2 then modulo a6pq2 2 else modulo (2 * a2p * -a4pq) 3
  let e2 := rst_iso (a' * (p ^ q : ℕ)) 0 0 e1
  have h1'' : surjvalp.v e2.a1 ≥ ofN 1 := by
    rw [rt_of_a1]
    assumption
  have h2'' : surjvalp.v e2.a2 = ofN 1 := by
    rw [r_of_a2, v_add_eq_min_v surjvalp]
    . assumption
    . rw [h2']
      apply lt_of_succ_le
      apply val_mul_ge_of_right_ge surjvalp
      apply val_mul_ge_of_right_ge surjvalp
      rw [nat_cast_pow, val_of_pow_uniformizer surjvalp]
      rw [lt_ofN 1 q] at hq
      exact succ_le_of_lt hq
  have h3'' : surjvalp.v e2.a3 ≥ ofN (q + 1) := by
    rw [r_of_a3]
    apply Enat.le_trans _ (surjvalp.v_add_ge_min_v _ _)
    apply le_min h3'
    rw [mul_comm a', mul_assoc, surjvalp.v_mul_eq_add_v, nat_cast_pow, val_of_pow_uniformizer, ←add_ofN]
    exact add_le_add (le_of_eq rfl) (val_mul_ge_of_right_ge surjvalp h1')
  have h4'' : surjvalp.v e2.a4 ≥ ofN (q + 2) := by
    rw [r_of_a4, factor_p_of_le_val evrp h4', rw_a4', factor_p_of_le_val evrp (le_of_eq h2'.symm), rw_a2', nat_cast_pow, factorize2 a' a2p (↑p) q, ←pow_add, ←mul_add, Int.add_comm a4pq]
    apply Enat.le_trans (le_min _ _) (surjvalp.v_add_ge_min_v _ _)
    . rw [Nat.add_succ q, Nat.succ_eq_add_one, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer, ←add_ofN]
      exact add_le_add (le_of_eq rfl) (succ_le_of_lt (val_poly_of_double_root hp a2p a4pq a6pq2 hdr').2)
    . rw [pow_two, factorize3 a' p q, ←pow_add]
      apply val_mul_ge_of_left_ge surjvalp _
      rw [val_of_pow_uniformizer]
      exact (le_ofN _ _).1 (Nat.add_le_add (le_of_eq rfl) (Nat.succ_le_of_lt hq))
  have h6'' : surjvalp.v e2.a6 ≥ ofN (2 * (q + 1)) := by
    rw [r_of_a6, nat_cast_pow]
    apply Enat.le_trans (le_min _ _) (surjvalp.v_add_ge_min_v _ _)
    . rw [factor_p_of_le_val evrp h6', rw_a6', factor_p_of_le_val evrp h4', rw_a4', factor_p_of_eq_val evrp h2', rw_a2', factorize4 a' a2p a4pq a6pq2 p q, ←pow_add, ←pow_add, ←pow_add, ←Nat.add_assoc, add_self_eq_mul_two q, ←mul_add, ←mul_add, Nat.mul_add, ←add_self_eq_mul_two 1, ←Nat.add_assoc, ←add_ofN, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer]
      exact add_le_add (le_of_eq rfl) (succ_le_of_lt (val_poly_of_double_root hp a2p a4pq a6pq2 hdr').1)
    . rw [mul_pow, ←pow_mul, mul_add, mul_one, Nat.mul_succ]
      apply val_mul_ge_of_right_ge surjvalp
      rw [val_of_pow_uniformizer, mul_comm q]
      exact (le_ofN _ _).1 (Nat.add_le_add (le_of_eq rfl) (Nat.succ_le_of_lt hq))
  let r := r + u0 ^ 2 + a * (p ^ q : ℕ)
  let t := t + u0 ^ 2 * s0 * a * (p ^ q : ℕ)
  kodaira_type_Is p hp e2 u0 r s0 t (m + 2) (q + 1) (Nat.lt_succ_of_lt hq) h1'' h2'' h3'' h4'' h6''
termination_by _ =>
  val_discr_to_nat (primeEVR hp).valtn e - (2 * q + 2)
decreasing_by
  simp_wf
  apply Nat.sub_lt_sub_left _ _
  . rw [lt_ofN, ofN_val_discr_to_nat]
    have val_d := v_discr_of_v_ai surjvalp e hq h1 h2 h3 h4 h6
    rw [←succ_ofN] at val_d
    exact lt_of_succ_le val_d
  . apply Nat.add_lt_add_right
    apply Nat.mul_lt_mul_of_pos_left _ (Nat.zero_lt_succ 1)
    exact Nat.lt_succ_self q


--lemma x : (0 < n ↔ 1 ≤ n) := by library_search
--lemma x (a b c d : ℤ) : a = b → c = d → a + c = b + d := by library_search
--lemma x (a b c d e : Int) : e + (a - b + c + d - e) = a - b + c + d := by ring

--set_option maxHeartbeats 400000

/-
example : 1 + 3 = 1 := by
  conv =>
    congr
    congr
    skip
    skip
    rw [(sorry : 1 = 2)]
  sorry
-/


def tate_small_prime (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) (u0 r0 s0 t0 : ℤ) : Kodaira × ℕ × ℕ × (ℤ × ℤ × ℤ × ℤ) :=
  if smallp : (p : ℤ) ≠ 2 ∧ (p : ℤ) ≠ 3 then (I 0, 0, 0, (0, 0, 0, 0)) else
  have p_is_2_or_3 : (p : ℤ) = 2 ∨ (p : ℤ) = 3 := by
    rw [Decidable.not_and] at smallp
    cases smallp with
    | inl p2 =>
      rw [Decidable.not_not] at p2
      exact Or.intro_left ((p:ℤ) = 3) p2
    | inr p3 =>
      rw [Decidable.not_not] at p3
      exact Or.intro_right ((p:ℤ) = 2) p3
  let (u, r, s, t) := (u0, r0, s0, t0)
  let evrp := primeEVR hp
  let navp := evrp.valtn
  --let valp := navp.v
  let Δ := e.discr
  let n := val_discr_to_nat navp e
  if testΔ : n = 0 then (I 0, 0, 1, (u, r, s, t)) else
  have hΔ : navp.v e.discr ≥ ofN 1 := by
    rw [(show ¬n = 0 ↔ 0 < n by simp [Nat.pos_iff_ne_zero]), lt_ofN, ofN_val_discr_to_nat] at testΔ
    exact succ_le_of_lt testΔ

  if test_b2 : navp.v e.b2 < ofN 1 then
    let (r1, t1) := if p = 2 then
      (modulo e.a3 2, modulo (e.a3 + e.a4) 2)
    else
      let r1' := modulo (-e.b2 * e.b4) 3
      (r1', modulo (e.a1 * r1' + e.a3) 3)
    let e1 := rst_iso r1 0 t1 e
    let r := r + r1 * u ^ 2
    let t := t + t1 * u ^ 3 + s * r1 * u ^ 2
    let c := if quad_root_in_ZpZ 1 e1.a1 (-e1.a2) p then n else gcd 2 n
    (I n, 1, c, (u, r, s, t))
  else
  have hb2 : navp.v e.b2 ≥ ofN 1 := le_of_not_lt test_b2

  let r1s1t1 := Model.move_singular_point_to_origin_triple evrp e.toModel

  let e1 := rst_triple e r1s1t1
  have He1 : rst_triple e (Model.move_singular_point_to_origin_triple evrp e.toModel) = e1 := by rfl
  let (r, s) := (r + r1s1t1.fst * u ^ 2, s + u * r1s1t1.snd.fst)
  let t := t + r1s1t1.snd.snd * u ^ 3 + s * r1s1t1.fst * u ^ 2

  have sing_origin : Model.local_singular_point navp e1.toModel (0, 0) := by
    simp [rst_iso]
    apply Model.move_singular_point_to_origin
    apply Model.singular_of_val_discr
    apply lt_of_succ_le hΔ

  have h3 : navp.v e1.a3 ≥ ofN 1 := by
    delta Model.local_singular_point at sing_origin
    have singular_dy := And.right (And.right sing_origin)
    simp [Model.dweierstrass_dy] at singular_dy
    rw [<-succ_ofN]
    apply succ_le_of_lt singular_dy

  have h4 : navp.v e1.a4 ≥ ofN 1 := by
    delta Model.local_singular_point at sing_origin
    have singular_dx := And.left (And.right sing_origin)
    simp [Model.dweierstrass_dx, pow_succ, sub_eq_add_neg, val_of_neg navp] at singular_dx
    rw [<-succ_ofN]
    apply succ_le_of_lt singular_dx

  have h6 : navp.v e1.a6 ≥ ofN 1 := by
    delta Model.local_singular_point at sing_origin
    have singular := And.left sing_origin
    simp [Model.weierstrass, pow_succ, sub_eq_add_neg, val_of_neg navp] at singular
    rw [<-succ_ofN]
    apply succ_le_of_lt singular

  if test_a6 : navp.v e1.a6 < ofN 2 then (II, n, 1, (u, r, s, t)) else
  have h6 : navp.v e1.a6 ≥ ofN 2 := le_of_not_lt test_a6

  if test_b8 : navp.v e1.b8 < ofN 3 then (III, n-1, 2, (u, r, s, t)) else
  have hb8 : navp.v e1.b8 ≥ ofN 3 := le_of_not_lt test_b8

  if test_b6 : navp.v e1.b6 < ofN 3 then
    let (a3p, a6p2) := (sub_val evrp e1.a3 1, sub_val evrp e1.a6 2)
    let c := if quad_root_in_ZpZ 1 a3p (-a6p2) p then 3 else 1
    (IV, n - 2, c, (u, r, s, t))
  else
  have hb6 : navp.v e1.b6 ≥ ofN 3 := le_of_not_lt test_b6

  have hb2 : navp.v e1.b2 ≥ ofN 1 := by
    rw [(show e1 = rst_iso r1s1t1.fst r1s1t1.snd.fst r1s1t1.snd.snd e by rfl)]
    apply v_rst_b2_of_small_char navp e r1s1t1.fst r1s1t1.snd.fst r1s1t1.snd.snd hb2
    exact small_char_div_12 p_is_2_or_3 navp

  have hdr_b2 : has_double_root 1 e1.a1 (-e1.a2) hp := by
    apply And.intro (val_of_one navp) _
    apply lt_of_succ_le
    rw [mul_one, ←neg_mul_right, sub_eq_add_neg, neg_neg, succ_ofN, pow_succ, pow_one]
    assumption

  let a3p := sub_val evrp e1.a3 1
  let a6p2 := sub_val evrp e1.a6 2

  have hdr_b6 : has_double_root 1 a3p (-a6p2) hp := by
    apply And.intro (val_of_one navp) _
    apply lt_of_succ_le
    rw [mul_one, ←neg_mul_right, sub_eq_add_neg, neg_neg, succ_ofN, pow_succ, pow_one]
    simp only [Model.b6] at hb6
    rw [factor_p_of_le_val evrp h3, factor_p_of_le_val evrp h6, factorize5, navp.v_mul_eq_add_v, val_of_pow_uniformizer, (show 3 = 2 + 1 by rfl), ←add_ofN] at hb6
    exact Enat.le_of_add_le_add_left hb6

  let s1 := double_root 1 e1.a1 (-e1.a2) p
  let t1 := double_root 1 a3p (-a6p2) p

  let e2 := rst_iso 0 s1 (p * t1) e1
  have He2 : rst_iso 0 s1 (p * t1) e1 = e2 := by rfl

  let t := t + t1 * u ^ 3

  have h1 : navp.v e2.a1 ≥ ofN 1 := by
    rw [st_of_a1, add_comm e1.a1, ←succ_ofN, ←mul_one 2]
    exact succ_le_of_lt (val_poly_of_double_root hp 1 e1.a1 (-e1.a2) hdr_b2).2

  have h2 : navp.v e2.a2 ≥ ofN 1 := by
    rw [←val_of_neg, st_of_a2, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg,
      neg_neg, Int.add_comm _ (s1 ^ 2), Int.add_comm (-e1.a2), ←Int.add_assoc,
      ←succ_ofN, ←one_mul (s1 ^ 2), mul_comm s1]
    exact succ_le_of_lt (val_poly_of_double_root hp 1 e1.a1 (-e1.a2) hdr_b2).1

  have h3' : navp.v e2.a3 ≥ ofN 2 := by
    rw [st_of_a3, ←mul_assoc, mul_comm 2, add_comm e1.a3, ←mul_one 2,
      factor_p_of_le_val evrp h3, pow_one, mul_assoc, ←mul_add, navp.v_mul_eq_add_v,
      (show (2 : ℕ) = 1 + 1 by rfl), ←add_ofN]
    apply add_le_add (le_of_eq (navp.v_uniformizer).symm)
    rw [←succ_ofN]
    exact succ_le_of_lt (val_poly_of_double_root hp 1 a3p (-a6p2) hdr_b6).2

  have hb8 : navp.v e2.b8 ≥ ofN 3 := by
    rw [st_of_b8]
    exact hb8

  have h6 : navp.v e2.a6 ≥ ofN 3 := by
    rw [←val_of_neg, st_of_a6, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg, neg_neg,
      Int.add_comm _ (_ ^ 2), Int.add_comm (-e1.a6), ←Int.add_assoc, mul_pow,
      factor_p_of_le_val evrp h3, factor_p_of_le_val evrp h6, neg_mul_right, factorize6,
      navp.v_mul_eq_add_v, (show 3 = 2 + 1 by rfl), ←add_ofN]
    apply add_le_add (le_of_eq (val_of_pow_uniformizer navp).symm)
    rw [←succ_ofN]
    exact succ_le_of_lt (val_poly_of_double_root hp 1 a3p (-a6p2) hdr_b6).1

  have h4 : navp.v e2.a4 ≥ ofN 2 := by
    have h4' : navp.v (e2.a4 ^ 2) ≥ ofN 3 := by
      rw [←Int.add_zero (e2.a4 ^ 2), ←add_neg_self e2.b8, ←Int.add_assoc, Int.add_comm (_ ^ 2)]
      delta Model.b8
      rw [sub_eq_add_neg, Int.add_assoc _ _ (_ ^ 2), Int.add_comm _ (_ ^ 2), pow_two,
        add_neg_self, Int.add_zero, ←sub_eq_add_neg _ (_ * _),
        (show e2.a1 * e2.a1 * e2.a6 - e2.a1 * e2.a3 * e2.a4 + 4 * e2.a2 * e2.a6 + e2.a2 * e2.a3 * e2.a3 - e2.a4 * e2.a4 = e2.b8 by rfl), sub_eq_add_neg, neg_mul_right, factor_p_of_le_val evrp hb8, factor_p_of_le_val evrp h1, factor_p_of_le_val evrp h3', factor_p_of_le_val evrp h6, neg_mul_right, factorize9]
      apply val_mul_ge_of_left_ge navp
      exact le_of_eq (val_of_pow_uniformizer navp).symm
    cases le_or_lt (navp.v e2.a4) (ofN 1) with
    | inl v_a4_le_1 =>
      apply False.elim
      rw [pow_two, navp.v_mul_eq_add_v] at h4'
      have x := Enat.le_trans h4' (add_le_add v_a4_le_1 v_a4_le_1)
      rw [add_ofN, ←le_ofN] at x
      exact Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ x))
    | inr v_a4_gt_1 =>
      exact succ_le_of_lt v_a4_gt_1

  let (a2p, a4p2, a6p3) := model_to_cubic evrp e2
  -- 18bcd – 4b³d + b²c² – 4c³ – 27d²

  if test_Δcubic : navp.v (Δcubic (model_to_cubic evrp e2)) = 0 then
    let c := 1 + count_roots_cubic 1 a2p a4p2 a6p3 p
    (Is 0, n - 4, c, (u, r, s, t))
  else
  if test_δcubic : navp.v (δmultiplicity (model_to_cubic evrp e2)) = 0 then
    have e2_cubic_has_double_root : cubic_has_double_root evrp e2 := by
      exact And.intro (pos_of_ne_zero test_Δcubic) test_δcubic

    --let r1 := p * (modulo (if p = 2 then a4p2 else a2p * a4p2) p)
    let e3 := move_cubic_double_root_to_origin_iso evrp e2
    --let r := r + u ^ 2 * r1
    --let t := t + u ^ 2 * s * r1
    have h1' : navp.v e3.a1 ≥ ofN 1 := by
      simp only [move_cubic_double_root_to_origin_iso]
      rw [rt_of_a1]
      exact h1

    have h2' : navp.v e3.a2 = ofN 1 := by
      have h2'' : navp.v e3.a2 ≥ ofN 1 := by
        simp only [move_cubic_double_root_to_origin_iso]
        rw [r_of_a2, factor_p_of_le_val evrp h2, pow_one, ←mul_assoc, mul_comm 3, mul_assoc, ←mul_add]
        apply val_mul_ge_of_left_ge
        exact le_of_eq navp.v_uniformizer.symm
      rw [factor_p_of_le_val evrp h2'', ←Enat.add_zero (ofN 1), navp.v_mul_eq_add_v, pow_one]
      apply congr_arg2 HAdd.hAdd
      . exact navp.v_uniformizer
      . exact (move_cubic_double_root_to_origin evrp e2 e2_cubic_has_double_root).1

    have h3 : navp.v e3.a3 ≥ ofN 2 := by
      simp only [move_cubic_double_root_to_origin_iso]
      rw [r_of_a3]
      apply val_add_ge_of_ge
      . exact h3'
      . rw [mul_assoc, factor_p_of_le_val evrp h1, mul_comm _ (_ ^ 1 * _), ←mul_assoc, ←mul_assoc, mul_comm _ (_ ^ 1), ←pow_succ, mul_assoc]
        apply val_mul_ge_of_left_ge
        rw [val_of_pow_uniformizer navp]
        exact le_of_eq rfl

    have h4' : navp.v e3.a4 ≥ ofN 3 := by
      have h4'' : navp.v e3.a4 ≥ ofN 2 := by
        simp only [move_cubic_double_root_to_origin_iso]
        rw [r_of_a4, factor_p_of_le_val evrp h4, factor_p_of_le_val evrp h2, factorize7]
        apply val_mul_ge_of_left_ge navp _
        exact le_of_eq (val_of_pow_uniformizer navp).symm
      rw [factor_p_of_le_val evrp h4'', navp.v_mul_eq_add_v, (show 3 = 2 + 1 by rfl), ←add_ofN]
      apply add_le_add
      . exact le_of_eq (val_of_pow_uniformizer navp).symm
      . rw [←succ_ofN 0]
        exact succ_le_of_lt (move_cubic_double_root_to_origin evrp e2 e2_cubic_has_double_root).2.1

    have h6 : navp.v e3.a6 ≥ ofN 4 := by
      have h6' : navp.v e3.a6 ≥ ofN 3 := by
        simp only [move_cubic_double_root_to_origin_iso]
        rw [r_of_a6, factor_p_of_le_val evrp h6, factor_p_of_le_val evrp h4, factor_p_of_le_val evrp h2, factorize8]
        apply val_mul_ge_of_left_ge navp _
        exact le_of_eq (val_of_pow_uniformizer navp).symm
      rw [factor_p_of_le_val evrp h6', navp.v_mul_eq_add_v, (show 4 = 3 + 1 by rfl), ←add_ofN]
      apply add_le_add
      . exact le_of_eq (val_of_pow_uniformizer navp).symm
      . rw [←succ_ofN 0]
        exact succ_le_of_lt (move_cubic_double_root_to_origin evrp e2 e2_cubic_has_double_root).2.2

    let (m, c, (r, t)) := kodaira_type_Is p hp e3 u r s t 1 2 (Nat.lt_succ_self 1) h1' h2' h3 h4' h6
    (Is m, n - m - 4, c, (u, r, s, t))
  else

  have e2_cubic_has_triple_root : cubic_has_triple_root evrp e2 := by
      exact And.intro (pos_of_ne_zero test_Δcubic) (pos_of_ne_zero test_δcubic)

  let e3 := move_cubic_triple_root_to_origin_iso evrp e2
  --let r1 := p * (modulo (if p = 2 then -a2p else -a6p3) p)
  --let r := r + u ^ 2 * r1
  --let t := t + u ^ 2 * s * r1
  have He3 : move_cubic_triple_root_to_origin_iso evrp e2 = e3 := by rfl

  have h2' : navp.v e3.a2 ≥ ofN 2 := by
    have h2'' : navp.v e3.a2 ≥ ofN 1 := by
      simp only [move_cubic_triple_root_to_origin_iso]
      rw [r_of_a2, factor_p_of_le_val evrp h2, pow_one, ←mul_assoc, mul_comm 3, mul_assoc, ←mul_add]
      apply val_mul_ge_of_left_ge
      exact le_of_eq navp.v_uniformizer.symm
    rw [factor_p_of_le_val evrp h2'', navp.v_mul_eq_add_v, pow_one, (show 2 = 1 + 1 by rfl), ←add_ofN]
    apply add_le_add
    . exact le_of_eq navp.v_uniformizer.symm
    . rw [←succ_ofN 0]
      exact succ_le_of_lt (move_cubic_triple_root_to_origin evrp e2 e2_cubic_has_triple_root).1

  have h3 : navp.v e3.a3 ≥ ofN 2 := by
    simp only [move_cubic_triple_root_to_origin_iso]
    rw [r_of_a3, factor_p_of_le_val evrp h1, pow_one]
    apply val_add_ge_of_ge navp
    . exact h3'
    . rw [←mul_assoc, mul_comm _ (p:ℤ), ←mul_assoc, ←pow_two, mul_assoc]
      apply val_mul_ge_of_left_ge navp (le_of_eq (val_of_pow_uniformizer navp).symm)

  have h6 : navp.v e3.a6 ≥ ofN 4 := by
    have h6' : navp.v e3.a6 ≥ ofN 3 := by
      simp only [move_cubic_triple_root_to_origin_iso]
      rw [r_of_a6, factor_p_of_le_val evrp h6, factor_p_of_le_val evrp h4, factor_p_of_le_val evrp h2, factorize8]
      apply val_mul_ge_of_left_ge navp _
      exact le_of_eq (val_of_pow_uniformizer navp).symm
    rw [factor_p_of_le_val evrp h6', navp.v_mul_eq_add_v, (show 4 = 3 + 1 by rfl), ←add_ofN]
    apply add_le_add
    . exact le_of_eq (val_of_pow_uniformizer navp).symm
    . rw [←succ_ofN 0]
      exact succ_le_of_lt (move_cubic_triple_root_to_origin evrp e2 e2_cubic_has_triple_root).2.2

  let a3p2 := sub_val evrp e3.a3 2
  let a6p4 := sub_val evrp e3.a6 4

  if discr_b6p4 : navp.v (a3p2 ^ 2 + 4 * a6p4) = 0 then
    let c := if quad_root_in_ZpZ 1 a3p2 (-a6p4) p then 3 else 1
    (IVs, n - 6, c, (u, r, s, t))
  else

  have h_b6p4 : has_double_root 1 a3p2 (-a6p4) hp := by
    apply And.intro (val_of_one navp) _
    apply pos_of_ne_zero
    rw [mul_one, ←neg_mul_right, sub_eq_add_neg, neg_neg]
    exact discr_b6p4

  let a := double_root 1 a3p2 (-a6p4) p
  have Ha : double_root 1 (sub_val evrp e3.a3 2) (-sub_val evrp e3.a6 4) p = a := by rfl

  let k := a * (p ^ 2 : ℕ)
  let e4 := rst_iso 0 0 k e3
  have He4 : rst_iso 0 0 (a * (p:ℤ) ^ 2) e3 = e4 := by rfl
  let t := t + k * u ^ 3
  have h3 : navp.v e4.a3 ≥ ofN 3 := by
    rw [t_of_a3, ←mul_one 2, factor_p_of_le_val evrp h3, ←mul_assoc (2*1), mul_comm ((2*1) * _), Nat.cast_pow, ←mul_add, Int.add_comm, (show 3 = 2 + 1 by rfl), ←add_ofN, navp.v_mul_eq_add_v]
    apply add_le_add
    . exact le_of_eq (val_of_pow_uniformizer navp).symm
    . rw [←succ_ofN 0]
      exact succ_le_of_lt (val_poly_of_double_root hp 1 a3p2 (-a6p4) h_b6p4).2

  if test_a4 : navp.v e4.a4 < ofN 4 then (IIIs, n - 7, 2, (u, r, s, t)) else
  have h4 : navp.v e4.a4 ≥ ofN 4 := le_of_not_lt test_a4

  if test_a6 : navp.v e4.a6 < ofN 6 then (IIs, n - 8, 1, (u, r, s, t)) else
  have h6 : navp.v e4.a6 ≥ ofN 6 := le_of_not_lt test_a6

  have h1 : navp.v e4.a1 ≥ ofN 1 := by
    rw [rt_of_a1]
    simp only [move_cubic_triple_root_to_origin_iso]
    rw [rt_of_a1]
    exact h1

  have h2 : navp.v e4.a2 ≥ ofN 2 := by
    rw [t_of_a2]
    exact h2'

  tate_small_prime p hp (ValidModel.pi_scaling evrp e4 h1 h2 h3 h4 h6) (p * u) r s t
termination_by _ =>
  val_discr_to_nat (primeEVR hp).valtn e
decreasing_by
  simp_wf
  simp only [He1, He2, He3, Ha]
  simp only [He4]
  rw [pi_scaling_val_discr_to_nat (primeEVR hp) e4 h1 h2 h3 h4 h6]
  have discr_eq : val_discr_to_nat (primeEVR hp).valtn e4 = val_discr_to_nat (primeEVR hp).valtn e := by
    rw [iso_rst_val_discr_to_nat]
    simp only [move_cubic_triple_root_to_origin_iso]
    rw [iso_rst_val_discr_to_nat, iso_rst_val_discr_to_nat]
    simp only [rst_triple]
    rw [iso_rst_val_discr_to_nat]
  rw [discr_eq]
  apply Nat.sub_lt_of_pos_le _ _ (Nat.zero_lt_succ 11)
  rw [le_ofN, ←discr_eq, ofN_val_discr_to_nat, (show Nat.succ 11 = 12 by rfl)]

  exact Model.val_discr_of_val_ai (primeEVR hp) e4.toModel h1 h2 h3 h4 h6




def tate_algorithm (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) : Kodaira × ℕ × ℕ × (ℤ × ℤ × ℤ × ℤ) :=
  if p = 2 then
    tate_small_prime 2 (Int.prime_2) e 1 0 0 0
  else if p = 3 then
    tate_small_prime 3 (Int.prime_3) e 1 0 0 0
  else
    tate_big_prime p hp e


def test_model : ValidModel ℤ := ⟨ ⟨1, -1, 1, -23130, -1322503⟩ , by simp⟩

end Int
