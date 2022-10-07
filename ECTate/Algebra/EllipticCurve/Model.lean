import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

variable {R : Type u} [IntegralDomain R]

section Obvious

lemma add4 : 2 + 2 = (4 : R) := by norm_num
lemma mul4 : 2 * 2 = (4 : R) := by norm_num

end Obvious

structure Model (R : Type u) [IntegralDomain R] where
  a1 : R
  a2 : R
  a3 : R
  a4 : R
  a6 : R

namespace Model

instance [Repr R] : Repr (Model R) := ⟨ λ (e : Model R) n => repr (e.a1, e.a2, e.a3, e.a4, e.a6)⟩

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
  -e.b2 * e.b2 * e.b8 - 8 * (e.b4 ^ 3) - 27 * e.b6 * e.b6 + 9 * e.b2 * e.b4 * e.b6

lemma discr_identity (e : Model R) : 1728 * e.discr = e.c4 ^ 4 - e.c6 ^ 2 :=
by
  simp only [c4, c6]
  sorry

def rst_iso (r s t : R) (e : Model R) : Model R := {
  a1 := e.a1 + 2*s,
  a2 := e.a2 - s*e.a1 + 3*r - s*s,
  a3 := e.a3 + r*e.a1 + 2*t,
  a4 := e.a4 - s*e.a3 + 2*r*e.a2 - (t+r*s)*e.a1 + 3*r*r - 2*s*t,
  a6 := e.a6 + r*e.a4 + r*r*e.a2 + r*r*r - t*(e.a3 + t + r*e.a1)
  }

/-
--def u_iso (u : R) (e : Model R) : Model R := iso 0 0 0 u e

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
  rw [(show 6 + (1 + 1) = 8 by norm_num)]
  rw [mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8), mul_assoc (u ^ 8)]
  rw [←mul_sub, ←mul_add, ←mul_add, ←mul_sub]

lemma u_discr (u : R) (e : Model R) : (u_iso u e).discr = u ^ 12 * e.discr :=
by
  simp only [discr, u_b2, u_b4, u_b6, u_b8]
  rw [neg_mul_right, ←mul_assoc _ (u ^ 2), mul_comm _ (u ^ 2), mul_comm (u ^ 8), ←mul_assoc, mul_comm, ←mul_assoc, ←mul_assoc, ←mul_assoc, ←mul_assoc]
  rw [mul_pow (u ^ 4) (b4 e), ←mul_assoc 8, mul_comm 8]
  rw [←mul_assoc 27, ←mul_assoc _ (u ^ 6), mul_comm 27, mul_comm _ (u ^ 6), ←mul_assoc, ←mul_assoc]
  rw [←mul_assoc 9, ←mul_assoc _ (u ^ 4), mul_comm 9, mul_comm _ (u ^ 4), ←mul_assoc, mul_comm (u ^ 4 * (u ^ 2 * 9 * b2 e) * b4 e), ←mul_assoc, ←mul_assoc, ←mul_assoc, ←mul_assoc]
  rw [←pow_add, ←pow_add, ←pow_mul, ←pow_add, ←pow_add, ←pow_add, (show 8 + 2 + 2 = 12 by norm_num), (show 4 * 3 = 12 by norm_num)]
  rw [mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12), mul_assoc (u ^ 12)]
  rw [←mul_sub (u ^ 12), ←mul_sub (u ^ 12), ←mul_add (u ^ 12)]


def rst_iso (r s t : R) (e : Model R) : Model R := iso r s t e
-/
lemma rst_b2 (r s t : R) (e : Model R) : (rst_iso r s t e).b2 = e.b2 + 12*r := by
  simp [rst_iso, b2, one_mul, one_pow, sub_eq_add_neg, mul_add, add_mul]
  rw [mul_comm _ (2*s), mul_assoc 2, add_assoc (e.a1*e.a1), ←add_assoc (2*(s*e.a1)), ←add_mul, add4, ←neg_mul_right]
  rw [←mul_assoc (2*s), mul_comm _ 2, ←mul_assoc 2, mul4, ←neg_mul_right, mul_assoc 4 s s]
  rw [add_comm (4*(s*e.a1)), add_comm (4*e.a2), add_assoc, add_assoc, add_comm (4*(s*s)), ←add_assoc]
  simp [←add_assoc (4*(s*e.a1))]
  rw [add_neg_self (4 * (s*e.a1)), add_assoc, add_assoc, neg_add_self (4*(s*s))]
  ring

lemma rst_b4 (r s t : R) (e : Model R) :
(rst_iso r s t e).b4 = e.b4 + r * (e.b2 + 6 * r) :=
by
  simp only [rst_iso, b2, b4, one_mul, one_pow, add_mul, mul_add, mul_sub, add_assoc, sub_eq_add_neg, neg_add, ←neg_mul_right, mul_assoc]
  apply congrArg
  rw [add_comm (2 * (s * (2 * t)))]
  simp only [←add_assoc, ←neg_mul_right, ←mul_assoc]
  simp only [add_assoc]
  rw [mul_comm (2 * s) 2, ←mul_assoc, add_left_neg (2 * 2 * s * t), add_zero]
  simp only [←add_assoc, (show 2 * 3 = (6 : R) by norm_num), mul_comm 6 r]
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
  rw [(show 2 * 2 = (4 : R) by norm_num), mul_comm 4]

lemma rst_b6 (r s t : R) (e : Model R) :
(rst_iso r s t e).b6 = e.b6 + 2*r*e.b4 + r*r*e.b2 + 4*r*r*r :=
by
  simp only [rst_iso, b2, b4, b6, one_mul, one_pow, add_mul, mul_add, mul_sub, add_assoc, sub_eq_add_neg, neg_add, ←neg_mul_right, mul_assoc]
  apply congrArg
  rw [add_comm (e.a3 * (r * e.a1)), add_comm, mul_comm e.a3 (r * e.a1), add_comm (2 * (r * (e.a1 * e.a3)))]
  simp only [←add_assoc, ←mul_assoc]
  rw [add_assoc _ (r * e.a1 * e.a3), add_self_eq_mul_two]
  simp only [←add_assoc, ←mul_assoc, ←add_assoc (4 * e.a6)]
  apply congrArg (. + 2 * r * e.a1 * e.a3)
  rw [add_comm _ (e.a3 * 2 * t), mul_assoc, mul_comm]
  simp only [←add_assoc]
  have add4 : 2 + 2 = (4 : R) := by norm_num;
  rw [mul_assoc 2 t e.a3, ←add_mul, add4, add_comm _ (-(4 * t * e.a3)), ←mul_assoc]
  simp only [←add_assoc, add_left_neg (4 * t * e.a3), zero_add]
  rw [add_comm _ (r * r * e.a1 * e.a1), mul_comm _ r, ←mul_assoc]
  simp only [add_assoc (r * r * e.a1 * e.a1)]
  apply congrArg
  rw [mul_comm _ 2, mul_assoc 2 _ t, mul_comm (r * e.a1), mul_assoc 2, mul_assoc 2, ←mul_assoc t r, ←add_mul, add4, add_comm]
  simp only [←add_assoc, ←mul_assoc, add_left_neg (4 * t * r * e.a1), zero_add]
  have mul4 : 2 * 2 = (4 : R) := by norm_num;
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
  simp only [rst_iso, b2, b4, b6, b8, one_mul, one_pow]
  --simp only [add_mul, mul_add, mul_sub, ←add_assoc, sub_eq_add_neg, neg_add, ←neg_mul_right, mul_assoc]
  sorry

lemma rst_discr (r s t : R) (e : Model R) : (rst_iso r s t e).discr = e.discr :=
by
  simp only [discr, rst_b2, rst_b4, rst_b6, rst_b8]
  sorry




def weierstrass (e : Model R) (P : R × R) : R :=
  P.2 ^ 2 + e.a1 * P.1 * P.2 + e.a3 * P.2 - P.1 ^ 3 - e.a2 * P.1 ^ 2 - e.a4 * P.1 - e.a6

--partial derivation library?

def dweierstrass_dx (e : Model R) (P : R × R) : R :=
  e.a1 * P.2 - 3 * P.1 ^ 2 - 2 * e.a2 * P.1 - e.a4

def dweierstrass_dy (e : Model R) (P : R × R) : R :=
  2 * P.2 + e.a1 * P.1 + e.a3

def var_change (r s t : R) (P' : R × R) : R × R :=
  (P'.1 + r, P'.2 + s * P'.1 + t)

theorem weierstrass_iso_eq_var_change (e : Model R) (P : R × R) : weierstrass (rst_iso r s t e) P = weierstrass e (var_change r s t P) := sorry

def rst_triple (e : Model R) (rst : R × R × R) : Model R :=
  rst_iso rst.fst rst.snd.fst rst.snd.snd e

lemma rst_iso_to_triple (e : Model R) (r s t : R) : rst_iso r s t e = rst_triple e (r, s, t) := rfl

end Model

structure ValidModel (R : Type u) [IntegralDomain R] extends Model R where
  discr_not_zero : toModel.discr ≠ 0

namespace ValidModel

instance [Repr R] : Repr (ValidModel R) := ⟨ λ (e : ValidModel R) n => repr e.toModel⟩

def rst_iso (r s t : R) (e : ValidModel R) : ValidModel R := {
  toModel := Model.rst_iso r s t e.toModel,
  discr_not_zero := by
    rw [Model.rst_discr]
    exact e.discr_not_zero
}

lemma rst_discr_valid (r s t : R) (e : ValidModel R) : (rst_iso r s t e).discr = e.discr :=
by
  exact Model.rst_discr r s t e.toModel

--more [simp] lemmas
lemma rt_of_a1 (e : ValidModel R) (r t : R) : (rst_iso r 0 t e).a1 = e.a1 := by simp only [rst_iso, Model.rst_iso, mul_zero, add_zero, one_mul]

lemma t_of_a2 (e : ValidModel R) (t : R) : (rst_iso 0 0 t e).a2 = e.a2 := by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma r_of_a2 (e : ValidModel R) (r : R) : (rst_iso r 0 0 e).a2 = e.a2 + 3 * r := by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma t_of_a3 (e : ValidModel R) (t : R) : (rst_iso 0 0 t e).a3 = e.a3 + 2 * t := by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma r_of_a3 (e : ValidModel R) (r : R) : (rst_iso r 0 0 e).a3 = e.a3 + r * e.a1 := by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma t_of_a4 (e : ValidModel R) (t : R) : (rst_iso 0 0 t e).a4 = e.a4 - t * e.a1 := by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma r_of_a4 (e : ValidModel R) (r : R) : (rst_iso r 0 0 e).a4 = e.a4 + 2 * r * e.a2 + 3 * r ^ 2 := by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, one_mul, add_zero, mul_assoc, ←pow_two r]

lemma t_of_a6 (e : ValidModel R) (t : R) : (rst_iso 0 0 t e).a6 = e.a6 - t * e.a3 - t ^ 2 := by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, one_mul, add_zero, mul_add, ←pow_two t, sub_eq_add_neg, neg_add, ←add_assoc]

lemma r_of_a6 (e : ValidModel R) (r : R) : (rst_iso r 0 0 e).a6 = e.a6 + r * e.a4 + r ^ 2 * e.a2 + r ^ 3 := by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, one_mul, add_zero, mul_assoc, ←pow_two r, ←pow_succ]

lemma st_of_a1 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).a1 = e.a1 + 2 * s := by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul]

lemma st_of_a2 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).a2 = e.a2 - s * e.a1 - s ^ 2 := by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul, add_zero, mul_assoc, ←pow_two s]

lemma st_of_a3 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).a3 = e.a3 + 2 * t := by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul, add_zero, mul_assoc, zero_mul]

lemma st_of_a4 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).a4 = e.a4 - s * e.a3 - t * e.a1 - 2 * s * t := by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul, add_zero, mul_assoc, zero_mul]

lemma st_of_a6 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).a6 = e.a6 - t * e.a3 - t ^ 2 := by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul, add_zero, mul_assoc, ←pow_two t, zero_mul, mul_add, sub_add]

lemma st_of_b8 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).b8 = e.b8 := by
  rw [rst_iso, Model.rst_b8]
  simp only [mul_zero, add_zero, zero_mul]

def rst_triple (e : ValidModel R) (rst : R × R × R) : ValidModel R :=
  rst_iso rst.fst rst.snd.fst rst.snd.snd e

lemma rst_iso_to_triple (e : ValidModel R) (r s t : R) : rst_iso r s t e = rst_triple e (r, s, t) := rfl



end ValidModel
