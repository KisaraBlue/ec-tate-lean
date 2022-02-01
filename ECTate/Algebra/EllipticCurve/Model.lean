import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

variable {R : Type u} [CommRing R]

section Obvious

lemma add4 : 2 + 2 = (4 : R) := by normNum
lemma mul4 : 2 * 2 = (4 : R) := by normNum

end Obvious

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

lemma b8_identity (e : Model R) : 4*e.b8 = e.b2*e.b6 - e.b4 ^ 2 :=
by
  simp only [b2, b4, b6]
  rw [add_mul, mul_add, mul_add, pow_succ, pow_one, add_mul, mul_add, mul_add]
  conv in e.a1 * e.a3 * (e.a1 * e.a3) => rw [←mul_assoc, mul_comm _ e.a1, ←mul_assoc, mul_assoc _ e.a3]
  rw [sub_eq_add_neg, neg_add, neg_add]
  simp only [←add_assoc]
  rw [add_comm _ (-(e.a1 * e.a1 * (e.a3 * e.a3)))]
  simp only [←add_assoc]
  rw [add_left_neg (e.a1 * e.a1 * (e.a3 * e.a3)), zero_add]
  conv in e.a1 * e.a1 * (4 * e.a6) => rw [←mul_assoc, mul_comm _ 4, mul_assoc]
  rw [neg_add]
  conv in -(e.a1 * e.a3 * (2 * e.a4)) => rw [←mul_assoc, mul_comm _ 2, mul_assoc, neg_mul_left]
  conv in -(2 * e.a4 * (e.a1 * e.a3)) => rw [mul_assoc, mul_comm e.a4, neg_mul_left]
  rw [←add_assoc, add_assoc _ _ (-2 * (e.a1 * e.a3 * e.a4)), ←add_mul, ←neg_add]
  conv in -(2 * e.a4 * (2 * e.a4)) => rw [←mul_assoc, mul_comm _ 2, ←mul_assoc, mul_assoc, neg_mul_left]
  rw [mul_assoc 4, ←mul_add 4, mul_assoc 4, ←mul_add 4]
  simp only [←neg_mul_left, ←sub_eq_add_neg, add4, mul4]
  rw [←mul_sub 4, ←mul_sub 4, sub_add_comm, sub_add_comm (e.a1 * e.a1 * e.a6), add_assoc _ (e.a2 * (e.a3 * e.a3)), add_comm (e.a2 * (e.a3 * e.a3)), ←add_assoc, ←mul_assoc, ←mul_assoc, mul_comm _ 4]
  rfl

def c4 (e : Model R) : R := e.b2 ^ 2 - 24*e.b4

def c6 (e : Model R) : R := -e.b2 ^ 3 + 36*e.b2*e.b4 - 216*e.b6

def discr (e : Model R) : R :=
  let (b2, b4, b6, b8) := (e.b2, e.b4, e.b6, e.b8);
  -b2*b2*b8 - 8*(b4 ^ 3) - 27*b6*b6 + 9*b2*b4*b6

lemma discr_identity (e : Model R) : 1728 * e.discr = e.c4 ^ 4 - e.c6 ^ 2 :=
by
  simp only [c4, c6]
  sorry

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
  simp only [u_iso, iso, b2, mul_zero, add_zero, sub_zero, zero_mul]
  rw [←mul_assoc (u * e.a1), mul_assoc u, mul_comm e.a1, ←mul_assoc]
  rw [←pow_one u, ←pow_add, mul_assoc, ←mul_assoc 4, mul_comm 4, mul_assoc _ 4]
  rw [←pow_mul, ←mul_add]

lemma u_b4 (u : R) (e : Model R) : (u_iso u e).b4 = u ^ 4 * e.b4 :=
by
  simp only [u_iso, iso, b4, mul_zero, add_zero, sub_zero, zero_mul]
  rw [←mul_assoc (u * e.a1), mul_assoc u, mul_comm e.a1, ←mul_assoc]
  rw [mul_comm u, ←pow_succ, mul_assoc, ←mul_assoc 2, mul_comm 2, mul_assoc _ 2]
  rw [←mul_add]

lemma u_b6 (u : R) (e : Model R) : (u_iso u e).b6 = u ^ 6 * e.b6 :=
by
  simp only [u_iso, iso, b6, mul_zero, add_zero, sub_zero, zero_mul]
  rw [←mul_assoc (u ^ 3 * e.a3), mul_assoc (u ^ 3), mul_comm e.a3, ←mul_assoc]
  rw [←pow_one u, ←pow_add, mul_assoc, ←mul_assoc 4, mul_comm 4, mul_assoc _ 4]
  rw [←pow_mul, ←mul_add]

lemma u_b8 (u : R) (e : Model R) : (u_iso u e).b8 = u ^ 8 * e.b8 :=
by
  simp only [u_iso, b8, iso, mul_zero, add_zero, sub_zero, zero_mul]
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
  rw [(show 6 + (1 + 1) = 8 by normNum)]
  rw [mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8)]
  rw [←mul_sub, ←mul_add, ←mul_add, ←mul_sub]

lemma u_discr (u : R) (e : Model R) : (u_iso u e).discr = u ^ 12 * e.discr :=
by
  simp only [discr, u_b2, u_b4, u_b6, u_b8]
  rw [neg_mul_right, ←mul_assoc _ (u ^ 2), mul_comm _ (u ^ 2), mul_comm (u ^ 8), ←mul_assoc, mul_comm, ←mul_assoc, ←mul_assoc, ←mul_assoc, ←mul_assoc]
  rw [mul_pow (u ^ 4) (b4 e), ←mul_assoc 8, mul_comm 8]
  rw [←mul_assoc 27, ←mul_assoc _ (u ^ 6), mul_comm 27, mul_comm _ (u ^ 6), ←mul_assoc, ←mul_assoc]
  rw [←mul_assoc 9, ←mul_assoc _ (u ^ 4), mul_comm 9, mul_comm _ (u ^ 4), ←mul_assoc, mul_comm (u ^ 4 * (u ^ 2 * 9 * b2 e) * b4 e), ←mul_assoc, ←mul_assoc, ←mul_assoc, ←mul_assoc]
  rw [←pow_add, ←pow_add, ←pow_mul, ←pow_add, ←pow_add, ←pow_add, (show 8 + 2 + 2 = 12 by normNum), (show 4 * 3 = 12 by normNum)]
  rw [mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12)]
  rw [←mul_sub (u ^ 12), ←mul_sub (u ^ 12), ←mul_add (u ^ 12)]

def rst_iso (r s t : R) (e : Model R) : Model R := iso r s t 1 e

lemma rst_b2 (r s t : R) (e : Model R) : (rst_iso r s t e).b2 = e.b2 + 12*r :=
by
  simp only [rst_iso, iso, b2, one_mul, one_pow]
  rw [mul_add, mul_sub, mul_add, mul_sub, add_mul, add_mul]
  rw [←mul_assoc, mul_comm e.a1 2, ←add_assoc, add_assoc (e.a1 * e.a1), mul_assoc, mul_assoc, mul_comm _ s, ←add_mul, ←mul_assoc (2 * s), mul_comm _ 2, ←mul_assoc 2, (show 2 * 2 = (4 : R) by normNum), mul_assoc 4]
  rw [sub_eq_add_neg, sub_eq_add_neg, add_comm _ (-(4 * (s * s))), ←add_assoc, add_assoc _ (4 * (s * s)), add_right_neg (4 * (s * s))]
  rw [add_zero, (show 2 + 2 = (4 : R) by normNum), add_assoc, add_comm (4 * e.a2), ←add_assoc (4 * (s * e.a1)), ←add_assoc (4 * (s * e.a1)), add_right_neg (4 * (s * e.a1)), zero_add]
  rw [←mul_assoc, (show 4 * 3 = (12 : R) by normNum), ←add_assoc]

lemma rst_b4 (r s t : R) (e : Model R) :
(rst_iso r s t e).b4 = e.b4 + r * (e.b2 + 6 * r) :=
by
  simp only [rst_iso, b2, b4, iso, one_mul, one_pow, add_mul, mul_add, mul_sub, add_assoc, sub_eq_add_neg, neg_add, ←neg_mul_right, mul_assoc]
  apply congrArg
  rw [add_comm (2 * (s * (2 * t)))]
  simp only [←add_assoc, ←neg_mul_right, ←mul_assoc]
  simp only [add_assoc]
  rw [mul_comm (2 * s) 2, ←mul_assoc, add_left_neg (2 * 2 * s * t), add_zero]
  simp only [←add_assoc, (show 2 * 3 = (6 : R) by normNum), mul_comm 6 r]
  apply congrArg (. + r * 6 * r)
  rw [add_comm _ (-(2 * s * e.a3))]
  simp only [←add_assoc, add_left_neg (2 * s * e.a3), zero_add]
  rw [mul_comm _ r, add_comm (2 * e.a4)]
  simp only [add_assoc (r * e.a1 * e.a1)]
  apply congrArg
  rw [add_comm, mul_comm _ s, ←mul_assoc, mul_comm s]
  simp only [←add_assoc, add_left_neg (2 * s * r * e.a1), zero_add]
  rw [add_comm, mul_comm _ e.a1, ←mul_assoc]
  simp only [←add_assoc, add_left_neg (e.a1 * 2 * t), zero_add]
  rw [(show 2 * 2 = (4 : R) by normNum), mul_comm 4]

lemma rst_b6 (r s t : R) (e : Model R) :
(rst_iso r s t e).b6 = e.b6 + 2*r*e.b4 + r*r*e.b2 + 4*r*r*r :=
by
  simp only [rst_iso, b2, b4, b6, iso, one_mul, one_pow, add_mul, mul_add, mul_sub, add_assoc, sub_eq_add_neg, neg_add, ←neg_mul_right, mul_assoc]
  apply congrArg
  rw [add_comm (e.a3 * (r * e.a1)), add_comm, mul_comm e.a3 (r * e.a1), add_comm (2 * (r * (e.a1 * e.a3)))]
  simp only [←add_assoc, ←mul_assoc]
  rw [add_assoc _ (r * e.a1 * e.a3), add_self_eq_mul_two]
  simp only [←add_assoc, ←mul_assoc, ←add_assoc (4 * e.a6)]
  apply congrArg (. + 2 * r * e.a1 * e.a3)
  rw [add_comm _ (e.a3 * 2 * t), mul_assoc, mul_comm]
  simp only [←add_assoc]
  have add4 : 2 + 2 = (4 : R) := by normNum;
  rw [mul_assoc 2 t e.a3, ←add_mul, add4, add_comm _ (-(4 * t * e.a3)), ←mul_assoc]
  simp only [←add_assoc, add_left_neg (4 * t * e.a3), zero_add]
  rw [add_comm _ (r * r * e.a1 * e.a1), mul_comm _ r, ←mul_assoc]
  simp only [add_assoc (r * r * e.a1 * e.a1)]
  apply congrArg
  rw [mul_comm _ 2, mul_assoc 2 _ t, mul_comm (r * e.a1), mul_assoc 2, mul_assoc 2, ←mul_assoc t r, ←add_mul, add4, add_comm]
  simp only [←add_assoc, ←mul_assoc, add_left_neg (4 * t * r * e.a1), zero_add]
  have mul4 : 2 * 2 = (4 : R) := by normNum;
  rw [mul_comm _ 2, ←mul_assoc, mul4, add_comm]
  simp only [←add_assoc, add_left_neg (4 * t * t), zero_add]
  simp only [add_assoc]
  apply congrArg
  --rw [mul_comm _ 2, ←mul_assoc, mul4]
  --apply congrArg
  --apply congrArg (. + 4 * r * r * r)
  --rw [mul_comm _ 4]
  --simp only [←mul_assoc]
  ring

lemma rst_b8 (r s t : R) (e : Model R) :
(rst_iso r s t e).b8 = e.b8 + 3*r*e.b6 + 3*r*r*e.b4 + r*r*r*e.b2 + 3*r*r*r*r :=
by
  simp only [rst_iso, b2, b4, b6, b8, iso, one_mul, one_pow]
  --simp only [add_mul, mul_add, mul_sub, ←add_assoc, sub_eq_add_neg, neg_add, ←neg_mul_right, mul_assoc]
  sorry

lemma rst_discr (r s t : R) (e : Model R) : (rst_iso r s t e).discr = e.discr :=
by
  simp only [discr, rst_b2, rst_b4, rst_b6, rst_b8]
  sorry

lemma decompose_iso (r s t u : R) (e : Model R) : iso r s t u e = u_iso u (rst_iso r s t e) := by
  simp only [u_iso, rst_iso, iso, zero_mul, mul_zero, zero_add, add_zero, sub_zero, one_pow, one_mul]

end Model

structure ValidModel (R : Type u) [CommRing R] extends Model R where
  discr_not_zero : toModel.discr ≠ 0

namespace ValidModel

def rst_iso (r s t : R) (e : ValidModel R) : ValidModel R := {
  toModel := Model.rst_iso r s t e.toModel,
  discr_not_zero := by
    rw [Model.rst_discr]
    exact e.discr_not_zero
}

lemma rst_discr_valid (r s t : R) (e : ValidModel R) : (rst_iso r s t e).discr = e.discr :=
by
  exact Model.rst_discr r s t e.toModel

def u_iso (u : R) (e : ValidModel R) (h : u ≠ 0) : ValidModel R := {
  toModel := Model.u_iso u e.toModel,
  discr_not_zero := by
    rw [Model.u_discr]
    --actually use a integral domain
    sorry
}

end ValidModel
