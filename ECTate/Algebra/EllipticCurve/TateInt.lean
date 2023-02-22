import ECTate.Algebra.EllipticCurve.Kronecker
import ECTate.Algebra.EllipticCurve.Model
import ECTate.Algebra.ValuedRing
import ECTate.Algebra.EllipticCurve.KodairaTypes
import ECTate.Data.Nat.Enat
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.LibrarySearch
import ECTate.Algebra.EllipticCurve.LocalEC
import Mathlib.Init.Algebra.Order




/- TODO list:
- show invariance under change of model
- show that Tate small prime agrees with big prime
- profile
- cleanup


Mathlib TODOs:
- attribute for ring
- deriving
- multiple lets
- does show_term use dot notation enough?
- Don't lint sorried stuff
- code folding for lean 4
-/


open Enat
open EnatValRing

open Kodaira


section ring_lemmas

variable {R : Type u} [CommRing R]

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


def tate_big_prime (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) :
  Kodaira × ℕ × ℕ × ReductionType × (ℤ × ℤ × ℤ × ℤ) :=
  let evrp := primeEVR hp
  let navp := evrp.valtn
  let c4 := e.c4
  let n := val_discr_to_nat navp e
  let ⟨vpj, k, integralInv⟩ :=
    match 3 * (primeEVR hp).valtn.v c4 with
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
  if !integralInv then
    let c6 := e.c6 / (↑u ^ 6)
    let Δ := e.discr / ofNat (u ^ 12)
    let ν := natAbs vpj
    match k with
      | 0 => let (c, R) := if kronecker (-c6) p = 1 then
                (ν, .SplitMultiplicative) else (gcd 2 ν, .NonSplitMultiplicative)
             (I ν, 1, c, R, (u, r, s, t))
      | 6 => (Is ν, 2,
              natAbs (3 + kronecker (if ν % 2 = 1 then
                     (Δ * c6 / (p ^ (ν + 9) : ℕ))
                else (Δ / (p ^ (ν + 6) : ℕ))) p),
              .Additive,
              (u, r, s, t))
      | _ => unreachable!
  else
    let c6 := e.c6 / (↑u ^ 6)
    let c4 := c4 / (↑u ^ 4)
    match k with
      | 0  => (I 0,  0, 1, .Good, (u, r, s, t))
      | 2  => (II,   2, 1, .Additive, (u, r, s, t))
      | 3  => (III,  2, 2, .Additive, (u, r, s, t))
      | 4  => (IV,   2,
               natAbs (2 + kronecker (-6 * c6 / (p * p)) p),
               .Additive,
               (u, r, s, t))
      | 6  => (Is 0, 2,
               1 + count_roots_cubic 4 0 (-3*c4 / (p*p)) (-c6 / (p*p*p)) p,
               .Additive,
               (u, r, s, t))
      | 8  => (IVs,  2,
               natAbs (2 + kronecker (-6 * c6 / (p ^ 4 : ℕ)) p),
               .Additive,
               (u, r, s, t))
      | 9  => (IIIs, 2, 2, .Additive, (u, r, s, t))
      | 10 => (IIs,  2, 1, .Additive, (u, r, s, t))
      | _  => unreachable!


def kodaira_type_Is (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) (u0 r0 s0 t0 : ℤ) (m q : ℕ)
  (hq : 1 < q) (h1 : (primeEVR hp).valtn.v e.a1 ≥ 1) (h2 : (primeEVR hp).valtn.v e.a2 = 1)
  (h3 : (primeEVR hp).valtn.v e.a3 ≥ q) (h4 : (primeEVR hp).valtn.v e.a4 ≥ q + 1)
  (h6 : (primeEVR hp).valtn.v e.a6 ≥ ↑(2 * q)) :
  ℕ × ℕ × ℤ × ℤ :=
  let evrp := primeEVR hp
  let surjvalp := evrp.valtn
  let (r, t) := (r0, t0)
  let a3q := sub_val evrp e.a3 q
  let a6q2 := sub_val evrp e.a6 (2 * q)
  have rw_a6 : sub_val evrp e.a6 (2 * q) = a6q2 := rfl --obvious rewriting lemmas that Lean should generate implicitly

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

  let e1 := rst_iso 0 0 (a * (p ^ q : ℕ)) e
  -- dbg_trace (_root_.repr e1)
  have h1' : surjvalp.v e1.a1 ≥ 1 := by rwa [rt_of_a1]
  have h2' : surjvalp.v e1.a2 = 1 := by rwa [t_of_a2]
  have h3' : surjvalp.v e1.a3 ≥ q + 1 := by
    rw [t_of_a3, factor_p_of_le_val evrp h3, ←mul_assoc, mul_comm (2*a),
      Nat.cast_pow, ←mul_add, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer]
    apply add_le_add (le_of_eq rfl)
    rw [add_comm, ←mul_one 2]
    exact succ_le_of_lt (val_poly_of_double_root hp 1 a3q (-a6q2) hdr).2
  have h4' : surjvalp.v e1.a4 ≥ (q + 1) := by
    rw [t_of_a4]
    apply le_trans _ (surjvalp.v_add_ge_min_v _ _)
    apply le_min h4
    rw [mul_assoc, val_neg, surjvalp.v_mul_eq_add_v, add_comm, surjvalp.v_mul_eq_add_v,
      Nat.cast_pow, val_of_pow_uniformizer]
    conv =>
      rhs
      rw [add_comm, add_assoc]
    rw [add_comm]
    apply add_le_add (le_of_eq rfl)
    exact le_trans h1 (le_add_right (surjvalp.v e.a1) _)
  have h6' : (primeEVR hp).valtn.v e1.a6 ≥ ↑(2 * q + 1) := by
    rw [t_of_a6, factor_p_of_le_val evrp h6, factor_p_of_le_val evrp h3, rw_a6, ←val_neg,
      sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg, neg_neg, neg_mul_right,
      Nat.cast_pow, pow_two, add_assoc, factorize1 a a3q ↑p q, ←pow_add, add_self_eq_mul_two,
      ←mul_add, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer, add_mul, ←pow_two,
      ←one_mul (a ^ 2), Int.add_comm]
    push_cast
    exact add_le_add (le_of_eq rfl) (succ_le_of_lt (val_poly_of_double_root hp 1 a3q (-a6q2) hdr).1)
  let t := t + u0 ^ 3 * a * (p ^ q : ℕ)
  let a2p := sub_val evrp e1.a2 1
  let a4pq := sub_val evrp e1.a4 (q + 1)
  let a6pq2 := sub_val evrp e1.a6 (2 * q + 1)
  --obvious rewriting lemmas that Lean should generate implicitly
  have rw_a2' : sub_val evrp e1.a2 1 = a2p := rfl
  have rw_a4' : sub_val evrp e1.a4 (q + 1) = a4pq := rfl
  have rw_a6' : sub_val evrp e1.a6 (2 * q + 1) = a6pq2 := rfl
  --less obvious lemma
  have rw_a2 : sub_val evrp e.a2 1 = a2p := by rw [←rw_a2', t_of_a2]
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
  -- dbg_trace (_root_.repr e2)
  have h1'' : surjvalp.v e2.a1 ≥ 1 := by rwa [rt_of_a1]
  have h2'' : surjvalp.v e2.a2 = 1 := by
    rwa [r_of_a2, v_add_eq_min_v surjvalp]
    rw [h2']
    apply lt_of_succ_le
    apply val_mul_ge_of_right_ge surjvalp
    apply val_mul_ge_of_right_ge surjvalp
    rw [Nat.cast_pow, val_of_pow_uniformizer surjvalp]
    rw [lt_ofN 1 q] at hq
    exact succ_le_of_lt hq
  have h3'' : surjvalp.v e2.a3 ≥ (q + 1) := by
    rw [r_of_a3]
    apply le_trans _ (surjvalp.v_add_ge_min_v _ _)
    apply le_min h3'
    rw [mul_comm a', mul_assoc, surjvalp.v_mul_eq_add_v, Nat.cast_pow, val_of_pow_uniformizer]
    exact add_le_add (le_of_eq rfl) (val_mul_ge_of_right_ge surjvalp h1')
  have h4'' : surjvalp.v e2.a4 ≥ (q + 2) := by
    rw [r_of_a4, factor_p_of_le_val evrp h4', rw_a4', factor_p_of_le_val evrp (le_of_eq h2'.symm),
      rw_a2', Nat.cast_pow, factorize2 a' a2p (↑p) q, ←pow_add, ←mul_add, add_comm a4pq]
    apply le_trans (le_min _ _) (surjvalp.v_add_ge_min_v _ _)
    . rw [Nat.add_succ q, Nat.succ_eq_add_one, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer]
      rw [Nat.cast_add, Nat.cast_one, add_assoc]
      rw [show 2 = 1 + 1 by norm_num, ← add_assoc, ← add_assoc]
      apply add_le_add (le_of_eq rfl)
      exact (succ_le_of_lt (val_poly_of_double_root hp a2p a4pq a6pq2 hdr').2)
    . rw [pow_two, factorize3 a' p q, ←pow_add]
      apply val_mul_ge_of_left_ge surjvalp _
      rw [val_of_pow_uniformizer]
      exact (le_ofN _ _).1 (Nat.add_le_add (le_of_eq rfl) (Nat.succ_le_of_lt hq))
  have h6'' : surjvalp.v e2.a6 ≥ ↑(2 * (q + 1)) := by
    rw [r_of_a6, Nat.cast_pow]
    apply le_trans (le_min _ _) (surjvalp.v_add_ge_min_v _ _)
    . rw [factor_p_of_le_val evrp h6', rw_a6', factor_p_of_le_val evrp h4', rw_a4',
        factor_p_of_eq_val evrp h2', rw_a2', factorize4 a' a2p a4pq a6pq2 p q, ←pow_add, ←pow_add,
        ←pow_add, ←Nat.add_assoc, add_self_eq_mul_two q, ←mul_add, ←mul_add, Nat.mul_add,
        ←add_self_eq_mul_two 1, ←Nat.add_assoc, surjvalp.v_mul_eq_add_v, val_of_pow_uniformizer]
      push_cast
      apply add_le_add (le_of_eq rfl)
      rw [show 1 = Enat.succ 0 by rfl]
      apply succ_le_of_lt
      have := (val_poly_of_double_root hp a2p a4pq a6pq2 hdr').1
      push_cast at this
      exact this
    . rw [mul_pow, ←pow_mul, mul_add, mul_one, Nat.mul_succ]
      apply val_mul_ge_of_right_ge surjvalp
      rw [val_of_pow_uniformizer, mul_comm q]
      exact (le_ofN _ _).1 (Nat.add_le_add (le_of_eq rfl) (Nat.succ_le_of_lt hq))
  let r := r + u0 ^ 2 + a' * (p ^ q : ℕ) -- TODO check these
  let t := t + u0 ^ 2 * s0 * a' * (p ^ q : ℕ)
  kodaira_type_Is p hp e2 u0 r s0 t (m + 2) (q + 1) (Nat.lt_succ_of_lt hq) h1'' h2'' h3'' h4'' h6''
termination_by _ =>
  val_discr_to_nat (primeEVR hp).valtn e - (2 * q + 2)
decreasing_by
  simp_wf
  apply Nat.sub_lt_sub_left _ _
  . rw [lt_ofN, ofN_val_discr_to_nat]
    exact lt_of_succ_le (v_discr_of_v_ai surjvalp e hq h1 h2 h3 h4 h6)
  . exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left q.lt_succ_self (Nat.zero_lt_succ 1)) 2


def tate_small_prime (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) (u0 : ℤ := 1) (r0 : ℤ :=0) (s0 : ℤ :=0) (t0 : ℤ :=0) :
  Kodaira × ℕ × ℕ × ReductionType × (ℤ × ℤ × ℤ × ℤ) :=
  --this function shouldn't be called with large primes (yet)
  if smallp : p ≠ 2 ∧ p ≠ 3 then unreachable! else
  have p_is_2_or_3 : (p : ℤ) = 2 ∨ (p : ℤ) = 3 := by
    rw [Decidable.not_and] at smallp
    cases smallp with
    | inl p2 =>
      rw [Decidable.not_not] at p2
      exact Or.intro_left ((p:ℤ) = 3) (by simp [p2])
    | inr p3 =>
      rw [Decidable.not_not] at p3
      exact Or.intro_right ((p:ℤ) = 2) (by simp [p3])
  let (u, r, s, t) := (u0, r0, s0, t0)
  let evrp := primeEVR hp
  let navp := evrp.valtn
  let n := val_discr_to_nat navp e
  if testΔ : n = 0 then (I 0, 0, 1, .Good, (u, r, s, t)) else -- TODO check
  have hΔ : navp.v e.discr ≥ 1 := by
    rw [show ¬n = 0 ↔ 0 < n by simp [Nat.pos_iff_ne_zero], lt_ofN, ofN_val_discr_to_nat] at testΔ
    exact succ_le_of_lt testΔ

  if test_b2 : navp.v e.b2 < 1 then
    let (r1, t1) := if p = 2 then
      (modulo e.a3 2, modulo (e.a3 + e.a4) 2)
    else
      let r1' := modulo (-e.b2 * e.b4) 3
      (r1', modulo (e.a1 * r1' + e.a3) 3)
    let e1 := rst_iso r1 0 t1 e
    let r := r + r1 * u ^ 2
    let t := t + t1 * u ^ 3 + s * r1 * u ^ 2
    let (c, R) := if quad_root_in_ZpZ 1 e1.a1 (-e1.a2) p then
      (n, .SplitMultiplicative) else (gcd 2 n, .NonSplitMultiplicative)
    (I n, 1, c, R, (u, r, s, t))
  else
  have hb2 : navp.v e.b2 ≥ 1 := le_of_not_lt test_b2

  let r1s1t1 := Model.move_singular_point_to_origin_triple evrp e.toModel

  let e1 := rst_triple e r1s1t1
  let (r, s) := (r + r1s1t1.fst * u ^ 2, s + u * r1s1t1.snd.fst)
  let t := t + r1s1t1.snd.snd * u ^ 3 + s * r1s1t1.fst * u ^ 2

  have sing_origin : Model.is_local_singular_point evrp e1.toModel (0, 0) := by
    apply Model.move_singular_point_to_origin evrp e.toModel (lt_of_succ_le hb2)
    apply Model.singular_of_val_discr
    apply quot_pos_val
    apply lt_of_succ_le hΔ

  have h3 : navp.v e1.a3 ≥ 1 := by
    delta Model.is_local_singular_point at sing_origin
    have singular_dy := And.right (And.right sing_origin)
    simp only [Model.dweierstrass_dy, mul_zero, add_zero, zero_add] at singular_dy
    apply @succ_le_of_lt 0
    apply pos_val_of_quot_zero singular_dy


  /- These two valuations can be proved at this point but are not used explicitely until stronger valuations are obtained
  have h4 : navp.v e1.a4 ≥ 1 := by
    delta Model.is_local_singular_point at sing_origin
    have singular_dx := And.left (And.right sing_origin)
    simp [Model.dweierstrass_dx, pow_succ, sub_eq_add_neg, val_neg navp] at singular_dx
    rw [<-succ_ofN]
    apply succ_le_of_lt singular_dx

  have h6 : navp.v e1.a6 ≥ 1 := by
    delta Model.is_local_singular_point at sing_origin
    have singular := And.left sing_origin
    simp [Model.weierstrass, pow_succ, sub_eq_add_neg, val_neg navp] at singular
    rw [<-succ_ofN]
    apply succ_le_of_lt singular
  -/

  if test_a6 : navp.v e1.a6 < 2 then (II, n, 1, .Additive, (u, r, s, t)) else
  have h6 : navp.v e1.a6 ≥ 2 := le_of_not_lt test_a6

  if test_b8 : navp.v e1.b8 < 3 then (III, n - 1, 2, .Additive, (u, r, s, t)) else
  have hb8 : navp.v e1.b8 ≥ 3 := le_of_not_lt test_b8

  if test_b6 : navp.v e1.b6 < 3 then
    let (a3p, a6p2) := (sub_val evrp e1.a3 1, sub_val evrp e1.a6 2)
    let c := if quad_root_in_ZpZ 1 a3p (-a6p2) p then 3 else 1
    (IV, n - 2, c, .Additive, (u, r, s, t))
  else
  have hb6 : navp.v e1.b6 ≥ 3 := le_of_not_lt test_b6

  have hb2 : navp.v e1.b2 ≥ 1 := by
    rw [show e1 = rst_iso r1s1t1.fst r1s1t1.snd.fst r1s1t1.snd.snd e by rfl]
    apply v_rst_b2_of_small_char navp e r1s1t1.fst r1s1t1.snd.fst r1s1t1.snd.snd hb2
    exact small_char_div_12 p_is_2_or_3 navp

  have hdr_b2 : has_double_root 1 e1.a1 (-e1.a2) hp := by
    apply And.intro (val_of_one navp) _
    apply lt_of_succ_le
    rwa [mul_one, ←neg_mul_right, sub_eq_add_neg, neg_neg, pow_succ, pow_one]

  let a3p := sub_val evrp e1.a3 1
  let a6p2 := sub_val evrp e1.a6 2

  have hdr_b6 : has_double_root 1 a3p (-a6p2) hp := by
    apply And.intro (val_of_one navp) _
    apply lt_of_succ_le
    rw [mul_one, ←neg_mul_right, sub_eq_add_neg, neg_neg, pow_succ, pow_one]
    simp only [Model.b6] at hb6
    rw [factor_p_of_le_val evrp h3, factor_p_of_le_val evrp h6, factorize5, navp.v_mul_eq_add_v,
      val_of_pow_uniformizer, show 3 = 2 + 1 by rfl] at hb6
    exact Enat.le_of_add_le_add_left hb6

  let s1 := double_root 1 e1.a1 (-e1.a2) p
  let t1 := double_root 1 a3p (-a6p2) p

  let e2 := rst_iso 0 s1 (p * t1) e1

  let t := t + t1 * u ^ 3

  have h1 : navp.v e2.a1 ≥ 1 := by
    rw [st_of_a1, add_comm e1.a1, ←mul_one 2]
    exact succ_le_of_lt (val_poly_of_double_root hp 1 e1.a1 (-e1.a2) hdr_b2).2

  have h2 : navp.v e2.a2 ≥ 1 := by
    rw [←val_neg, st_of_a2, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg,
      neg_neg, add_comm _ (s1 ^ 2), add_comm (-e1.a2), ←add_assoc,
      ← one_mul (s1 ^ 2), mul_comm s1]
    exact succ_le_of_lt (val_poly_of_double_root hp 1 e1.a1 (-e1.a2) hdr_b2).1

  have h3' : navp.v e2.a3 ≥ 2 := by
    rw [st_of_a3, ←mul_assoc, mul_comm 2, add_comm e1.a3, ←mul_one 2,
      factor_p_of_le_val evrp h3, pow_one, mul_assoc, ←mul_add, navp.v_mul_eq_add_v,
      show (2 : Enat) = 1 + 1 by norm_num]
    apply add_le_add (le_of_eq navp.v_uniformizer.symm)
    exact succ_le_of_lt (val_poly_of_double_root hp 1 a3p (-a6p2) hdr_b6).2

  have hb8 : navp.v e2.b8 ≥ 3 := by
    rw [st_of_b8]
    exact hb8

  have h6 : navp.v e2.a6 ≥ 3 := by
    rw [←val_neg, st_of_a6, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_add, neg_neg, neg_neg,
      add_comm _ (_ ^ 2), add_comm (-e1.a6), ←add_assoc, mul_pow,
      factor_p_of_le_val evrp h3, factor_p_of_le_val evrp h6, neg_mul_right, factorize6,
      navp.v_mul_eq_add_v, show 3 = 2 + 1 by rfl]
    apply add_le_add (le_of_eq (val_of_pow_uniformizer navp).symm)
    exact succ_le_of_lt (val_poly_of_double_root hp 1 a3p (-a6p2) hdr_b6).1

  have h4 : navp.v e2.a4 ≥ 2 := by
    have h4' : navp.v (e2.a4 ^ 2) ≥ 3 := by
      rw [←add_zero (e2.a4 ^ 2), ←add_neg_self e2.b8, ←add_assoc, add_comm (_ ^ 2)]
      delta Model.b8
      rw [sub_eq_add_neg, add_assoc _ _ (_ ^ 2), add_comm _ (_ ^ 2), pow_two,
        add_neg_self, add_zero, ←sub_eq_add_neg _ (_ * _),
        show e2.a1 * e2.a1 * e2.a6 - e2.a1 * e2.a3 * e2.a4 +
          4 * e2.a2 * e2.a6 + e2.a2 * e2.a3 * e2.a3 - e2.a4 * e2.a4 = e2.b8 by rfl, sub_eq_add_neg,
          neg_mul_right, factor_p_of_le_val evrp hb8, factor_p_of_le_val evrp h1,
          factor_p_of_le_val evrp h3', factor_p_of_le_val evrp h6, neg_mul_right, factorize9]
      apply val_mul_ge_of_left_ge navp
      exact le_of_eq (val_of_pow_uniformizer navp).symm
    cases le_or_lt (navp.v e2.a4) 1 with
    | inl v_a4_le_1 =>
      apply False.elim
      rw [pow_two, navp.v_mul_eq_add_v] at h4'
      have x := le_trans h4' (add_le_add v_a4_le_1 v_a4_le_1)
      simp at x
      -- simpa using
    | inr v_a4_gt_1 =>
      exact succ_le_of_lt v_a4_gt_1

  let (a2p, a4p2, a6p3) := model_to_cubic evrp e2
  -- 18bcd – 4b³d + b²c² – 4c³ – 27d²

  if test_Δcubic : navp.v (Δcubic (model_to_cubic evrp e2)) = 0 then -- TODO don't recompute a2p,a4pw above
    let c := 1 + count_roots_cubic 1 a2p a4p2 a6p3 p
    (Is 0, n - 4, c, .Additive, (u, r, s, t))
  else
  -- dbg_trace (_root_.repr e2)
  -- dbg_trace (model_to_cubic evrp e2)
  if test_δcubic : navp.v (δmultiplicity (model_to_cubic evrp e2)) = 0 then
    have e2_cubic_has_double_root : cubic_has_double_root evrp e2 :=
      And.intro (pos_of_ne_zero test_Δcubic) test_δcubic

    --let r1 := p * (modulo (if p = 2 then a4p2 else a2p * a4p2) p)
    let e3 := move_cubic_double_root_to_origin_iso evrp e2
    -- dbg_trace (_root_.repr e3)
    --let r := r + u ^ 2 * r1
    --let t := t + u ^ 2 * s * r1
    have h1' : navp.v e3.a1 ≥ 1 := by
      simp only [move_cubic_double_root_to_origin_iso]
      rwa [rt_of_a1]

    have h2' : navp.v e3.a2 = 1 := by
      have h2'' : navp.v e3.a2 ≥ 1 := by
        simp only [move_cubic_double_root_to_origin_iso]
        rw [r_of_a2, factor_p_of_le_val evrp h2, pow_one, ←mul_assoc, mul_comm 3, mul_assoc, ←mul_add]
        apply val_mul_ge_of_left_ge
        exact le_of_eq navp.v_uniformizer.symm
      rw [factor_p_of_le_val evrp h2'', navp.v_mul_eq_add_v, pow_one, navp.v_uniformizer,
        (move_cubic_double_root_to_origin evrp e2 e2_cubic_has_double_root).1, add_zero]

    have h3 : navp.v e3.a3 ≥ 2 := by
      simp only [move_cubic_double_root_to_origin_iso, r_of_a3]
      apply val_add_ge_of_ge _ h3'
      rw [mul_assoc, factor_p_of_le_val evrp h1, mul_comm _ (_ ^ 1 * _), ←mul_assoc, ←mul_assoc,
        mul_comm _ (_ ^ 1), ←pow_succ', mul_assoc]
      apply val_mul_ge_of_left_ge
      rw [val_of_pow_uniformizer navp]
      exact le_refl _

    have h4' : navp.v e3.a4 ≥ 3 := by
      have h4'' : navp.v e3.a4 ≥ 2 := by
        simp only [move_cubic_double_root_to_origin_iso]
        rw [r_of_a4, factor_p_of_le_val evrp h4, factor_p_of_le_val evrp h2, factorize7]
        apply val_mul_ge_of_left_ge navp _
        exact le_of_eq (val_of_pow_uniformizer navp).symm
      rw [factor_p_of_le_val evrp h4'', navp.v_mul_eq_add_v, show 3 = 2 + 1 by rfl]
      apply add_le_add
      . exact le_of_eq (val_of_pow_uniformizer navp).symm
      . exact succ_le_of_lt (move_cubic_double_root_to_origin evrp e2 e2_cubic_has_double_root).2.1

    have h6 : navp.v e3.a6 ≥ 4 := by
      have h6' : navp.v e3.a6 ≥ 3 := by
        simp only [move_cubic_double_root_to_origin_iso]
        rw [r_of_a6, factor_p_of_le_val evrp h6, factor_p_of_le_val evrp h4, factor_p_of_le_val evrp h2, factorize8]
        apply val_mul_ge_of_left_ge navp _
        exact le_of_eq (val_of_pow_uniformizer navp).symm
      rw [factor_p_of_le_val evrp h6', navp.v_mul_eq_add_v, show 4 = 3 + 1 by rfl]
      apply add_le_add
      . exact le_of_eq (val_of_pow_uniformizer navp).symm
      . exact succ_le_of_lt (move_cubic_double_root_to_origin evrp e2 e2_cubic_has_double_root).2.2

    let (m, c, (r, t)) := kodaira_type_Is p hp e3 u r s t 1 2 (Nat.lt_succ_self 1) h1' h2' h3 h4' h6
    (Is m, n - m - 4, c, .Additive, (u, r, s, t))
  else

  have e2_cubic_has_triple_root : cubic_has_triple_root evrp e2 :=
    And.intro (pos_of_ne_zero test_Δcubic) (pos_of_ne_zero test_δcubic)

  let e3 := move_cubic_triple_root_to_origin_iso evrp e2
  --let r1 := p * (modulo (if p = 2 then -a2p else -a6p3) p)
  --let r := r + u ^ 2 * r1
  --let t := t + u ^ 2 * s * r1
  have He3 : move_cubic_triple_root_to_origin_iso evrp e2 = e3 := by rfl

  have h2' : navp.v e3.a2 ≥ 2 := by
    have h2'' : navp.v e3.a2 ≥ 1 := by
      simp only [move_cubic_triple_root_to_origin_iso]
      rw [r_of_a2, factor_p_of_le_val evrp h2, pow_one, ←mul_assoc, mul_comm 3, mul_assoc, ←mul_add]
      apply val_mul_ge_of_left_ge
      exact le_of_eq navp.v_uniformizer.symm
    rw [factor_p_of_le_val evrp h2'', navp.v_mul_eq_add_v, pow_one, show 2 = 1 + 1 by rfl]
    apply add_le_add
    . exact le_of_eq navp.v_uniformizer.symm
    . exact succ_le_of_lt (move_cubic_triple_root_to_origin evrp e2 e2_cubic_has_triple_root).1

  have h3 : navp.v e3.a3 ≥ 2 := by
    simp only [move_cubic_triple_root_to_origin_iso]
    rw [r_of_a3, factor_p_of_le_val evrp h1, pow_one]
    apply val_add_ge_of_ge navp
    . exact h3'
    . rw [←mul_assoc, mul_comm _ (p:ℤ), ←mul_assoc, ←pow_two, mul_assoc]
      apply val_mul_ge_of_left_ge navp (le_of_eq (val_of_pow_uniformizer navp).symm)

  have h6 : navp.v e3.a6 ≥ 4 := by
    have h6' : navp.v e3.a6 ≥ 3 := by
      simp only [move_cubic_triple_root_to_origin_iso]
      rw [r_of_a6, factor_p_of_le_val evrp h6, factor_p_of_le_val evrp h4, factor_p_of_le_val evrp h2, factorize8]
      apply val_mul_ge_of_left_ge navp _
      exact le_of_eq (val_of_pow_uniformizer navp).symm
    rw [factor_p_of_le_val evrp h6', navp.v_mul_eq_add_v, show 4 = 3 + 1 by rfl]
    apply add_le_add
    . exact le_of_eq (val_of_pow_uniformizer navp).symm
    . exact succ_le_of_lt (move_cubic_triple_root_to_origin evrp e2 e2_cubic_has_triple_root).2.2

  let a3p2 := sub_val evrp e3.a3 2
  let a6p4 := sub_val evrp e3.a6 4

  if discr_b6p4 : navp.v (a3p2 ^ 2 + 4 * a6p4) = 0 then
    let c := if quad_root_in_ZpZ 1 a3p2 (-a6p4) p then 3 else 1
    (IVs, n - 6, c, .Additive, (u, r, s, t))
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
  have h3 : navp.v e4.a3 ≥ 3 := by
    rw [t_of_a3, ←mul_one 2, factor_p_of_le_val evrp h3, ←mul_assoc (2*1), mul_comm ((2*1) * _),
      Nat.cast_pow, ←mul_add, add_comm, show 3 = 2 + 1 by rfl, navp.v_mul_eq_add_v]
    apply add_le_add
    . exact le_of_eq (val_of_pow_uniformizer navp).symm
    . exact succ_le_of_lt (val_poly_of_double_root hp 1 a3p2 (-a6p4) h_b6p4).2

  if test_a4 : navp.v e4.a4 < 4 then (IIIs, n - 7, 2, .Additive, (u, r, s, t)) else
  have h4 : navp.v e4.a4 ≥ 4 := le_of_not_lt test_a4

  if test_a6 : navp.v e4.a6 < 6 then (IIs, n - 8, 1, .Additive, (u, r, s, t)) else
  have h6 : navp.v e4.a6 ≥ 6 := le_of_not_lt test_a6

  have h1 : navp.v e4.a1 ≥ 1 := by
    rw [rt_of_a1]
    simp only [move_cubic_triple_root_to_origin_iso]
    rw [rt_of_a1]
    exact h1

  have h2 : navp.v e4.a2 ≥ 2 := by
    rw [t_of_a2]
    exact h2'

  tate_small_prime p hp (ValidModel.pi_scaling evrp e4 h1 h2 h3 h4 h6) (p * u) r s t
termination_by _ =>
  val_discr_to_nat (primeEVR hp).valtn e
decreasing_by
  simp_wf
  simp only [He3, Ha]
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
  rw [le_ofN, ←discr_eq, ofN_val_discr_to_nat, show Nat.succ 11 = 12 by rfl]

  exact Model.val_discr_of_val_ai (primeEVR hp) e4.toModel h1 h2 h3 h4 h6




/--
Tate's algorithm takes an elliptic curve over the integers and a prime and returns the
- Kodaira type
- Conductor exponent
- Tamagawa number
- Reduction type (split/nonsplit multiplicative or additive) and urst isomorphism to a minimal curve?
-/
def tate_algorithm (p : ℕ) (hp : nat_prime p) (e : ValidModel ℤ) :
  Kodaira × ℕ × ℕ × ReductionType × (ℤ × ℤ × ℤ × ℤ) :=
  if p = 2 then
    tate_small_prime 2 Int.prime_2 e
  else if p = 3 then
    tate_small_prime 3 Int.prime_3 e
  else
    tate_big_prime p hp e


def test_model : ValidModel ℤ := ⟨⟨1, -1, 1, -23130, -1322503⟩, by simp⟩

#eval tate_algorithm 2 prime_2 test_model

end Int
