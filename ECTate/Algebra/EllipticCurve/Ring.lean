import Mathlib.Algebra.Ring.Basic

/-
class IntegralDomain (R : Type u) extends CommRing R where
  non_zero : 0 ≠ 1
  mul_non_zero (a b : R) : a ≠ 0 → b ≠ 0 → a * b ≠ 0

class Ideal (I : Type u) extends

class DiscValRing (R : Type u) extends CommRing R where
-/
variable {R : Type u} [CommRing R]

structure Model (R : Type u) [CommRing R] where
  a1 : R
  a2 : R
  a3 : R
  a4 : R
  a6 : R

namespace Model

def b2 (e : Model R) : R := e.a1 * e.a1 + 4 * e.a2

def b4 (e : Model R) : R := e.a1 * e.a3 + 2 * e.a4

def b6 (e : Model R) : R := e.a3 * e.a3 + 4 * e.a6

def b8 (e : Model R) : R :=
  e.a1*e.a1*e.a6 - e.a1*e.a3*e.a4 + 4*e.a2*e.a6 + e.a2*e.a3*e.a3 - e.a4*e.a4

lemma b8_identity (e : Model R) : 4*e.b8 = e.b2*e.b6 - e.b4 ^ 2 := by sorry

def c4 (e : Model R) : R := e.b2 ^ 2 - 24*e.b4

def c6 (e : Model R) : R := -e.b2 ^ 3 + 36*e.b2*e.b4 - 216*e.b6

def discr (e : Model R) : R :=
  let (b2, b4, b6, b8) := (e.b2, e.b4, e.b6, e.b8);
  -b2*b2*b8 - 8*(b4 ^ 3) - 27*b6*b6 + 9*b2*b4*b6

lemma discr_identity (e : Model R) : 1728*e.discr = e.c4 ^ 4 - e.c6 ^ 2 := by sorry

def iso (r s t u : R) (e : Model R) : Model R := {
  a1 := u * (e.a1 + 2*s),
  a2 := u ^ 2 * (e.a2 - s*e.a1 + 3*r - s*s),
  a3 := u ^ 3 * (e.a3 + r*e.a1 + 2*t),
  a4 := u ^ 4 * (e.a4 - s*e.a3 + 2*r*e.a2 - (t+r*s)*e.a1 + 3*r*r - 2*s*t),
  a6 := u ^ 6 * (e.a6 + r*e.a4 + r*r*e.a2 + r*r*r - t*(e.a3 + t + r*e.a1))
  }

def u_iso (u : R) (e : Model R) : Model R := iso 0 0 0 u e

lemma u_b2 (u : R) (e : Model R) : (u_iso u e).b2 = u ^ 2 * e.b2 :=
by
  show (u * (e.a1 + 2*0)) * (u * (e.a1 + 2*0)) + 4 * (u ^ 2 * (e.a2 - 0*e.a1 + 3*0 - 0*0)) = u ^ 2 * b2 e
  simp
  rw [←mul_assoc (u * e.a1), mul_assoc u, mul_comm e.a1, ←mul_assoc]
  rw [←pow_one u, ←pow_add, mul_assoc, ←mul_assoc 4, mul_comm 4, mul_assoc _ 4]
  rw [←pow_mul, ←mul_add]
  rfl

lemma u_b4 (u : R) (e : Model R) : (u_iso u e).b4 = u ^ 4 * e.b4 :=
by
  show (u * (e.a1 + 2*0)) * (u ^ 3 * (e.a3 + 0*e.a1 + 2*0)) + 2 * (u ^ 4 * (e.a4 - 0*e.a3 + 2*0*e.a2 - (0+0*0)*e.a1 + 3*0*0 - 2*0*0)) = u ^ 4 * b4 e
  simp
  rw [←mul_assoc (u * e.a1), mul_assoc u, mul_comm e.a1, ←mul_assoc]
  rw [mul_comm u, ←pow_succ, mul_assoc, ←mul_assoc 2, mul_comm 2, mul_assoc _ 2]
  rw [←mul_add]
  rfl

lemma u_b6 (u : R) (e : Model R) : (u_iso u e).b6 = u ^ 6 * e.b6 :=
by
  show (u ^ 3 * (e.a3 + 0*e.a1 + 2*0)) * (u ^ 3 * (e.a3 + 0*e.a1 + 2*0)) + 4 * (u ^ 6 * (e.a6 + 0*e.a4 + 0*0*e.a2 + 0*0*0 - 0*(e.a3 + 0 + 0*e.a1))) = u ^ 6 * b6 e
  simp
  rw [←mul_assoc (u ^ 3 * e.a3), mul_assoc (u ^ 3), mul_comm e.a3, ←mul_assoc]
  rw [←pow_one u, ←pow_add, mul_assoc, ←mul_assoc 4, mul_comm 4, mul_assoc _ 4]
  rw [←pow_mul, ←mul_add]
  rfl

lemma u_b8 (u : R) (e : Model R) : (u_iso u e).b8 = u ^ 8 * e.b8 :=
by
  show (u * (e.a1 + 2*0))*(u * (e.a1 + 2*0))*(u ^ 6 * (e.a6 + 0*e.a4 + 0*0*e.a2 + 0*0*0 - 0*(e.a3 + 0 + 0*e.a1))) - (u * (e.a1 + 2*0))*(u ^ 3 * (e.a3 + 0*e.a1 + 2*0))*(u ^ 4 * (e.a4 - 0*e.a3 + 2*0*e.a2 - (0+0*0)*e.a1 + 3*0*0 - 2*0*0)) + 4*(u ^ 2 * (e.a2 - 0*e.a1 + 3*0 - 0*0))*(u ^ 6 * (e.a6 + 0*e.a4 + 0*0*e.a2 + 0*0*0 - 0*(e.a3 + 0 + 0*e.a1))) + (u ^ 2 * (e.a2 - 0*e.a1 + 3*0 - 0*0))*(u ^ 3 * (e.a3 + 0*e.a1 + 2*0))*(u ^ 3 * (e.a3 + 0*e.a1 + 2*0)) - (u ^ 4 * (e.a4 - 0*e.a3 + 2*0*e.a2 - (0+0*0)*e.a1 + 3*0*0 - 2*0*0))*(u ^ 4 * (e.a4 - 0*e.a3 + 2*0*e.a2 - (0+0*0)*e.a1 + 3*0*0 - 2*0*0)) = u ^ 8 * b8 e
  simp
  rw [←mul_assoc (u * e.a1), mul_assoc u, mul_comm e.a1, ←mul_assoc u u]
  rw [←mul_assoc _ (u ^ 6), mul_comm _ (u ^ 6), ←mul_assoc, ←mul_assoc]
  conv in u * u => rw [←pow_one u, ←pow_add]
  rw [mul_assoc u, ←mul_assoc e.a1, mul_comm e.a1, ←mul_assoc u, ←mul_assoc u]
  rw [←mul_assoc _ (u ^ 4), mul_comm _ (u ^ 4), ←mul_assoc (u ^ 4), ←mul_assoc (u ^ 4)]
  conv in u * u ^ 3 => rw [←pow_one u, ←pow_mul, ←pow_add]
  rw [←mul_assoc 4, mul_comm 4, ←mul_assoc _ (u ^ 6), mul_comm _ (u ^ 6), ←mul_assoc (u ^ 6), ←mul_assoc (u ^ 6)]
  rw [←mul_assoc _ (u ^ 3), mul_comm _ (u ^ 3), ←mul_assoc _ (u ^ 3), mul_comm _ (u ^ 3), ←mul_assoc (u ^ 3), ←mul_assoc (u ^ 3), ←mul_assoc _ (u ^ 2)]
  conv in u ^ 4 * e.a4 * (u ^ 4 * e.a4) => rw [←mul_assoc, mul_comm _ (u ^ 4), ←mul_assoc]
  rw [←pow_add, ←pow_add, ←pow_add, ←pow_add]
  show u ^ 8 * e.a1 * e.a1 * e.a6 - u ^ 8 * e.a1 * e.a3 * e.a4 + u ^ 8 * 4 * e.a2 * e.a6 + u ^ 8 * e.a2 * e.a3 * e.a3 - u ^ 8 * e.a4 * e.a4 = u ^ 8 * b8 e
  rw [mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8)]
  rw [←mul_sub, ←mul_add, ←mul_add, ←mul_sub]
  rfl

lemma u_discr (u : R) (e : Model R) : (u_iso u e).discr = u ^ 12 * e.discr :=
by
  show -(u_iso u e).b2*(u_iso u e).b2*(u_iso u e).b8 - 8*((u_iso u e).b4 ^ 3) - 27*(u_iso u e).b6*(u_iso u e).b6 + 9*(u_iso u e).b2*(u_iso u e).b4*(u_iso u e).b6 = u ^ 12 * e.discr
  conv in (u_iso u e).b2 => rw [u_b2]
  conv in (u_iso u e).b4 => rw [u_b4]
  conv in (u_iso u e).b6 => rw [u_b6]
  rw [u_b8, neg_mul_right, ←mul_assoc _ (u ^ 2), mul_comm _ (u ^ 2), mul_comm (u ^ 8), ←mul_assoc, mul_comm, ←mul_assoc, ←mul_assoc, ←mul_assoc, ←mul_assoc]
  rw [mul_pow (u ^ 4) (b4 e), ←mul_assoc 8, mul_comm 8]
  rw [←mul_assoc 27, ←mul_assoc _ (u ^ 6), mul_comm 27, mul_comm _ (u ^ 6), ←mul_assoc, ←mul_assoc]
  rw [←mul_assoc 9, ←mul_assoc _ (u ^ 4), mul_comm 9, mul_comm _ (u ^ 4), ←mul_assoc, mul_comm (u ^ 4 * (u ^ 2 * 9 * b2 e) * b4 e), ←mul_assoc, ←mul_assoc, ←mul_assoc, ←mul_assoc]
  rw [←pow_add, ←pow_add, ←pow_mul, ←pow_add, ←pow_add, ←pow_add]
  rw [mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12)]
  rw [←mul_sub (u ^ 12), ←mul_sub (u ^ 12), ←mul_add (u ^ 12)]
  rfl

def rst_iso (r s t : R) (e : Model R) : Model R := iso r s t 1 e

lemma rst_b2 (r s t : R) (e : Model R) : (rst_iso r s t e).b2 = e.b2 + 12*r :=
by
  show (1 * (e.a1 + 2*s)) * (1 * (e.a1 + 2*s)) + 4 * (1 ^ 2 * (e.a2 - s*e.a1 + 3*r - s*s)) = e.b2 + 12*r
  rw [pow_succ, pow_one]
  simp
  rw [mul_add, mul_sub, mul_add, mul_sub, add_mul, add_mul]
  rw [←mul_assoc, mul_comm e.a1 2, ←add_assoc, add_assoc (e.a1 * e.a1), mul_assoc, mul_assoc, mul_comm _ s, ←add_mul, ←mul_assoc (2 * s), mul_comm _ 2, ←mul_assoc 2, mul_assoc (2 * 2)]
  rw [sub_eq_add_neg, sub_eq_add_neg, add_comm _ (-(4*(s*s))), ←add_assoc, add_assoc _ (2 * 2 *(s * s)), add_comm (2 * 2 *(s * s))]
  rw [neg_mul_left, ←add_mul]
  sorry

lemma rst_b4 (r s t : R) (e : Model R) :
(rst_iso r s t e).b4 = e.b4 + r * (e.b2 + 6 * r) :=
by
  sorry

lemma rst_b6 (r s t : R) (e : Model R) :
(rst_iso r s t e).b6 = e.b6 + 2*r*e.b4 + r*r*e.b2 + 4*r*r*r :=
by
  sorry

lemma rst_b8 (r s t : R) (e : Model R) :
(rst_iso r s t e).b8 = e.b8 + 3*r*e.b6 + 3*r*r*e.b4 + r*r*r*e.b2 + 3*r*r*r*r :=
by
  sorry

def ai_divible (u : R) (e : Model R) : Prop := ∃ (a1' a2' a3' a4' a6' : R),
u * a1' = e.a1 ∧ u ^ 2 * a2' = e.a2 ∧ u ^ 3 * a3' = e.a3 ∧ u ^ 4 * a4' = e.a4 ∧ u ^ 6 * a6' = e.a6

def u_inv_iso {u : R} {e : Model R} (h : ai_divible u e) : Model R :=
  match h with
  | ⟨a1', a2', a3', a4', a6', x⟩ => {a1 := a1', a2 := a2', a3 := a3', a4 := a4', a6 := a6'}

end Model

structure ValidModel (R : Type u) [CommRing R] extends Model R where
  discr_not_zero : toModel.discr ≠ 0

namespace ValidModel



end ValidModel
