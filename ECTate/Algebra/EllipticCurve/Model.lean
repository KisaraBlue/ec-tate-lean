import ECTate.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpTrace
import Mathlib.Tactic.LibrarySearch


section ring_with_neg
namespace ring_neg
variable {R : Type _} [Ring R]
lemma sub_add_comm {x y z : R} : (x - y) + z = x + z - y :=
by rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_assoc, add_comm z]
lemma neg_mul_neg {y z : R} : -y * -z = y * z :=
by simp [← neg_mul_left, ← neg_mul_right, neg_neg]
lemma neg_pow_three {y : R} : (- y)^3 = - (y ^ 3) :=
by simp [pow_succ, mul_assoc]; simp [neg_mul_neg]; rw [neg_mul_left]
lemma sub_sub {x y z : R} : (x - (y - z)) = x + z - y :=
by simp [sub_eq_add_neg, neg_add, add_assoc, add_comm z]
lemma add_sub {x y z : R} : (x + (y - z)) = x + y - z :=
by simp [sub_eq_add_neg, add_assoc]
-- lemma neg_pow_four {y : R} : (- y)^4 = (y ^ 4) :=
-- by simp [pow_succ]; asso simp [neg_mul_neg]
lemma neg_add_eq_sub {y z : R} : - y + z = z - y :=
by rw [sub_eq_add_neg, add_comm z]
lemma sub_add_cancel {y z : R} : y - z + z = y :=
by rw [sub_eq_add_neg, add_assoc]; simp
lemma add_sub_cancel {y z : R} : y + z - z = y :=
by rw [sub_eq_add_neg, add_assoc]; simp

lemma sub_eq_iff_eq_add {x y z : R} : y - z = x ↔ y = x + z :=
by
  constructor
  . intro h
    rw [← h]
    simp [sub_add_cancel]
  . intro h
    rw [h]
    simp [add_sub_cancel]

lemma eq_sub_iff_add_eq {x y z : R} : x = y - z ↔ x + z = y :=
by
  constructor
  . intro h
    rw [h]
    simp [sub_add_cancel]
  . intro h
    rw [← h]
    simp [add_sub_cancel]

end ring_neg
end ring_with_neg

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
deriving Inhabited

namespace Model

instance [Repr R] : Repr (Model R) := ⟨ λ (e : Model R) _ => repr (e.a1, e.a2, e.a3, e.a4, e.a6)⟩

def b2 (e : Model R) : R := e.a1 * e.a1 + 4 * e.a2

def b4 (e : Model R) : R := e.a1 * e.a3 + 2 * e.a4

def b6 (e : Model R) : R := e.a3 * e.a3 + 4 * e.a6

def b8 (e : Model R) : R :=
  e.a1*e.a1*e.a6 - e.a1*e.a3*e.a4 + 4*e.a2*e.a6 + e.a2*e.a3*e.a3 - e.a4*e.a4

open ring_neg in
lemma b8_identity (e : Model R) : 4*e.b8 = e.b2*e.b6 - e.b4 ^ 2 :=
by
  simp only [b2, b4, b6, b8]
  simp [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, sub_add]
  simp [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm]
  ring

def c4 (e : Model R) : R := e.b2 ^ 2 - 24*e.b4

def c6 (e : Model R) : R := -e.b2 ^ 3 + 36*e.b2*e.b4 - 216*e.b6

def discr (e : Model R) : R :=
  -e.b2 * e.b2 * e.b8 - 8 * (e.b4 ^ 3) - 27 * e.b6 * e.b6 + 9 * e.b2 * e.b4 * e.b6
open ring_neg in
lemma discr_identity (e : Model R) : 1728 * e.discr = e.c4 ^ 3 - e.c6 ^ 2 :=
by
  simp only [c4, c6, discr]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left, ← neg_mul_right,
    mul_add, add_mul, mul_sub, sub_mul, sub_add]
  rw [(by ring : 1728 * (e.b2 * e.b2 * e.b8) = 432 * (e.b2 * e.b2 * (4 * e.b8)))]
  rw [b8_identity]
  simp [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left, ← neg_mul_right,
    mul_add, add_mul, mul_sub, sub_mul, sub_add, add_sub]
  simp [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm, neg_add_eq_sub, add_sub]
  ring

def rst_iso (r s t : R) (e : Model R) : Model R := {
  a1 := e.a1 + 2*s,
  a2 := e.a2 - s*e.a1 + 3*r - s*s,
  a3 := e.a3 + r*e.a1 + 2*t,
  a4 := e.a4 - s*e.a3 + 2*r*e.a2 - (t+r*s)*e.a1 + 3*r*r - 2*s*t,
  a6 := e.a6 + r*e.a4 + r*r*e.a2 + r*r*r - t*(e.a3 + t + r*e.a1)
  }

lemma rst_b2 (r s t : R) (e : Model R) : (rst_iso r s t e).b2 = e.b2 + 12*r := by
  simp [rst_iso, b2, one_mul, one_pow, sub_eq_add_neg, mul_add, add_mul]
  rw [mul_comm _ (2*s), mul_assoc 2, add_assoc (e.a1*e.a1), ←add_assoc (2*(s*e.a1)), ←add_mul, add4, ←neg_mul_right]
  rw [←mul_assoc (2*s), mul_comm _ 2, ←mul_assoc 2, mul4, ←neg_mul_right, mul_assoc 4 s s]
  rw [add_comm (4*(s*e.a1)), add_comm (4*e.a2), add_assoc, add_assoc, add_comm (4*(s*s)), ←add_assoc]
  simp [←add_assoc (4*(s*e.a1))]
  rw [add_assoc, add_assoc, neg_add_self (4*(s*s))]
  ring

lemma rst_b4 (r s t : R) (e : Model R) :
  (rst_iso r s t e).b4 = e.b4 + r * (e.b2 + 6 * r) :=
by
  simp only [rst_iso, b2, b4, one_mul, one_pow, add_mul, mul_add, mul_sub, add_assoc, sub_eq_add_neg, neg_add]
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

open ring_neg in
lemma rst_b8 (r s t : R) (e : Model R) :
  (rst_iso r s t e).b8 = e.b8 + 3*r*e.b6 + 3*r*r*e.b4 + r*r*r*e.b2 + 3*r*r*r*r :=
by
  simp only [rst_iso, b2, b4, b6, b8, one_mul, one_pow]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul]
  simp [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm, neg_add_eq_sub, add_sub, sub_add]
  ring

open ring_neg in
lemma rst_discr (r s t : R) (e : Model R) : (rst_iso r s t e).discr = e.discr :=
by
  simp only [discr, rst_b2, rst_b4, rst_b6, rst_b8]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul]
  rw [(by ring : b2 e * (12 * r) * b8 e = b2 e * (3 * r) * (4 * b8 e)),
      (by ring : 12 * r * b2 e * b8 e = 3 * r * b2 e * (4 * b8 e)),
      (by ring : 12 * r * (12 * r) * b8 e = 3 * r * 12 * r * (4 * b8 e))]
  simp only [b8_identity]
  simp [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul]
  simp [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm, neg_add_eq_sub, add_sub, sub_add]
  ring

def weierstrass (e : Model R) (P : R × R) : R :=
  P.2 ^ 2 + e.a1 * P.1 * P.2 + e.a3 * P.2 - P.1 ^ 3 - e.a2 * P.1 ^ 2 - e.a4 * P.1 - e.a6

--partial derivation library?

def dweierstrass_dx (e : Model R) (P : R × R) : R :=
  e.a1 * P.2 - 3 * P.1 ^ 2 - 2 * e.a2 * P.1 - e.a4

def dweierstrass_dy (e : Model R) (P : R × R) : R :=
  2 * P.2 + e.a1 * P.1 + e.a3

def var_change (r s t : R) (P' : R × R) : R × R :=
  (P'.1 + r, P'.2 + s * P'.1 + t)

theorem weierstrass_iso_eq_var_change (e : Model R) (P : R × R) :
  weierstrass (rst_iso r s t e) P = weierstrass e (var_change r s t P) := sorry

def rst_triple (e : Model R) (rst : R × R × R) : Model R :=
  rst_iso rst.fst rst.snd.fst rst.snd.snd e

lemma rst_iso_to_triple (e : Model R) (r s t : R) : rst_iso r s t e = rst_triple e (r, s, t) := rfl

end Model

structure ValidModel (R : Type u) [IntegralDomain R] extends Model R where
  discr_not_zero : toModel.discr ≠ 0

namespace ValidModel
instance [Repr R] : Repr (ValidModel R) := ⟨ λ (e : ValidModel R) _ => repr e.toModel⟩
-- #eval repr ({a1 := 0,a2 := 0, a3:=0,a4:=0,a6:=1, discr_not_zero := by norm_num : ValidModel ℤ})


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
lemma rt_of_a1 (e : ValidModel R) (r t : R) : (rst_iso r 0 t e).a1 = e.a1 :=
by simp only [rst_iso, Model.rst_iso, mul_zero, add_zero, one_mul]

lemma t_of_a2 (e : ValidModel R) (t : R) : (rst_iso 0 0 t e).a2 = e.a2 :=
by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma r_of_a2 (e : ValidModel R) (r : R) : (rst_iso r 0 0 e).a2 = e.a2 + 3 * r :=
by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma t_of_a3 (e : ValidModel R) (t : R) : (rst_iso 0 0 t e).a3 = e.a3 + 2 * t :=
by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma r_of_a3 (e : ValidModel R) (r : R) : (rst_iso r 0 0 e).a3 = e.a3 + r * e.a1 :=
by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma t_of_a4 (e : ValidModel R) (t : R) : (rst_iso 0 0 t e).a4 = e.a4 - t * e.a1 :=
by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero, add_zero, one_mul]

lemma r_of_a4 (e : ValidModel R) (r : R) : (rst_iso r 0 0 e).a4 = e.a4 + 2 * r * e.a2 + 3 * r ^ 2 :=
by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul,
  sub_zero, mul_zero, one_mul, add_zero, mul_assoc, ←pow_two r]

lemma t_of_a6 (e : ValidModel R) (t : R) : (rst_iso 0 0 t e).a6 = e.a6 - t * e.a3 - t ^ 2 :=
by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero, mul_zero,
  one_mul, add_zero, mul_add, ←pow_two t, sub_eq_add_neg, neg_add, ←add_assoc]

lemma r_of_a6 (e : ValidModel R) (r : R) :
  (rst_iso r 0 0 e).a6 = e.a6 + r * e.a4 + r ^ 2 * e.a2 + r ^ 3 :=
by simp only [rst_iso, Model.rst_iso, one_pow, zero_mul, sub_zero,
  mul_zero, one_mul, add_zero, mul_assoc, ←pow_two r, ←pow_succ]

lemma st_of_a1 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).a1 = e.a1 + 2 * s :=
by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul]

lemma st_of_a2 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).a2 = e.a2 - s * e.a1 - s ^ 2 :=
by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul, add_zero, mul_assoc, ←pow_two s]

lemma st_of_a3 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).a3 = e.a3 + 2 * t :=
by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul, add_zero, mul_assoc, zero_mul]

lemma st_of_a4 (e : ValidModel R) (s t : R) :
  (rst_iso 0 s t e).a4 = e.a4 - s * e.a3 - t * e.a1 - 2 * s * t :=
by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul, add_zero, mul_assoc, zero_mul]

lemma st_of_a6 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).a6 = e.a6 - t * e.a3 - t ^ 2 :=
by simp only [rst_iso, Model.rst_iso, one_pow, mul_zero, one_mul,
  add_zero, mul_assoc, ←pow_two t, zero_mul, mul_add, sub_add]

lemma st_of_b8 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).b8 = e.b8 := by
  rw [rst_iso, Model.rst_b8]
  simp only [mul_zero, add_zero, zero_mul]

def rst_triple (e : ValidModel R) (rst : R × R × R) : ValidModel R :=
  rst_iso rst.fst rst.snd.fst rst.snd.snd e

lemma rst_iso_to_triple (e : ValidModel R) (r s t : R) : rst_iso r s t e = rst_triple e (r, s, t) :=
rfl

end ValidModel
