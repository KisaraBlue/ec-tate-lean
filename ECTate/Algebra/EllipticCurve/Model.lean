import ECTate.Algebra.Ring.Basic
import ECTate.Algebra.CharP.Basic
import ECTate.FieldTheory.PerfectClosure
import ECTate.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpTrace
import Mathlib.Tactic.PrintPrefix
import Mathlib.Tactic.LibrarySearch
import Mathlib.Util.WhatsNew



#print CommGroup.toDivisionCommMonoid
#print AddCommGroup.toDivisionCommMonoid -- TODO LOL
attribute [instance] AddCommGroup.toDivisionCommMonoid
section ring_with_neg
namespace ring_neg
variable {R : Type _} [Ring R]
lemma sub_add_comm' {x y z : R} : (x - y) + z = x + z - y :=
by rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_assoc, add_comm z]
lemma neg_mul_neg {y z : R} : -y * -z = y * z :=
by simp [← neg_mul_left, ← neg_mul_right, neg_neg]
lemma neg_pow_three {y : R} : (- y)^3 = - (y ^ 3) :=
by simp [pow_succ, mul_assoc]; simp [neg_mul_neg]; rw [neg_mul_left]
lemma sub_sub' {x y z : R} : (x - (y - z)) = x + z - y :=
by simp [sub_eq_add_neg, neg_add, add_assoc, add_comm z]
-- lemma add_sub {x y z : R} : (x + (y - z)) = x + y - z :=
-- by simp [sub_eq_add_neg, add_assoc]
-- lemma neg_pow_four {y : R} : (- y)^4 = (y ^ 4) :=
-- by simp [pow_succ]; asso simp [neg_mul_neg]
-- lemma neg_add_eq_sub {y z : R} : - y + z = z - y :=
-- by rw [sub_eq_add_neg, add_comm z]
lemma sub_add_cancel {y z : R} : y - z + z = y :=
by rw [sub_eq_add_neg, add_assoc]; simp
lemma add_sub_cancel {y z : R} : y + z - z = y :=
by rw [sub_eq_add_neg, add_assoc]; simp
lemma sub_neg {y z : R} : y - -z = y + z :=
by simp [sub_eq_add_neg]


-- lemma sub_eq_iff_eq_add {x y z : R} : y - z = x ↔ y = x + z :=
-- by
--   constructor
--   . intro h
--     rw [← h]
--     simp [sub_add_cancel]
--   . intro h
--     rw [h]
--     simp [add_sub_cancel]

-- lemma eq_sub_iff_add_eq {x y z : R} : x = y - z ↔ x + z = y :=
-- by
--   constructor
--   . intro h
--     rw [h]
--     simp [sub_add_cancel]
--   . intro h
--     rw [← h]
--     simp [add_sub_cancel]

lemma neg_eq_neg_iff {y z : R} : -z = -y ↔ y = z :=
by rw [← zero_add (-z), ← sub_eq_add_neg,
       ← zero_add (-y), ← sub_eq_add_neg,
       sub_eq_iff_eq_add, sub_add_comm, add_zero, eq_sub_iff_add_eq, zero_add]

end ring_neg
end ring_with_neg

section Obvious
variable {R : Type u} [IntegralDomain R]


lemma add4 : 2 + 2 = (4 : R) := by norm_num
lemma mul4 : 2 * 2 = (4 : R) := by norm_num

end Obvious

/-- A model of a (possibly singular) elliptic curve is given
by `a` invariants $$a₁, a₂, a₃, a₄, a₆$$ which represent the curve
$$
y^2 + a₁ xy + a₃ y =  x^ 3 + a₂ x ^ 2 + a₄ x + a₆
$$
-/
structure Model (R : Type u) [IntegralDomain R] where
  a1 : R
  a2 : R
  a3 : R
  a4 : R
  a6 : R
deriving Inhabited, DecidableEq

namespace Model
variable {R : Type u} [IntegralDomain R]

instance [Repr R] : Repr (Model R) := ⟨λ (e : Model R) _ => repr (e.a1, e.a2, e.a3, e.a4, e.a6)⟩

def b2 (e : Model R) : R := e.a1 * e.a1 + 4 * e.a2

def b4 (e : Model R) : R := e.a1 * e.a3 + 2 * e.a4

def b6 (e : Model R) : R := e.a3 * e.a3 + 4 * e.a6

def b8 (e : Model R) : R :=
  e.a1*e.a1*e.a6 - e.a1*e.a3*e.a4 + 4*e.a2*e.a6 + e.a2*e.a3*e.a3 - e.a4*e.a4

/-- From Connell -/
def b5 (e : Model R) : R := e.a1 * e.a4 - 2 * e.a2 * e.a3

def b7 (e : Model R) : R := e.a1 * (e.a3 ^ 2 - 12 * e.a6) + 8 * e.a3 * e.a4

open ring_neg in
lemma b8_identity (e : Model R) : 4*e.b8 = e.b2*e.b6 - e.b4 ^ 2 :=
by
  simp only [b2, b4, b6, b8]
  simp only [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub', pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, sub_add, pow_zero, mul_one]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm']
  ring

def c4 (e : Model R) : R := e.b2 ^ 2 - 24*e.b4

def c6 (e : Model R) : R := -e.b2 ^ 3 + 36*e.b2*e.b4 - 216*e.b6

def discr (e : Model R) : R :=
  -e.b2 * e.b2 * e.b8 - 8 * e.b4 ^ 3 - 27 * e.b6 * e.b6 + 9 * e.b2 * e.b4 * e.b6

open ring_neg in
lemma discr_identity (e : Model R) : 1728 * e.discr = e.c4 ^ 3 - e.c6 ^ 2 :=
by
  simp only [c4, c6, discr]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, sub_add]
  rw [(by ring : 1728 * (e.b2 * e.b2 * e.b8) = 432 * (e.b2 * e.b2 * (4 * e.b8)))]
  rw [b8_identity]
  simp [neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left, ← neg_mul_right,
    mul_add, add_mul, mul_sub, sub_mul, sub_add, add_sub]
  simp [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm', neg_add_eq_sub, add_sub]
  ring

def rst_iso (r s t : R) (e : Model R) : Model R := {
  a1 := e.a1 + 2*s,
  a2 := e.a2 - s*e.a1 + 3*r - s*s,
  a3 := e.a3 + r*e.a1 + 2*t,
  a4 := e.a4 - s*e.a3 + 2*r*e.a2 - (t+r*s)*e.a1 + 3*r*r - 2*s*t,
  a6 := e.a6 + r*e.a4 + r*r*e.a2 + r*r*r - t*(e.a3 + t + r*e.a1) }

lemma rst_b2 (r s t : R) (e : Model R) : (rst_iso r s t e).b2 = e.b2 + 12*r := by
  simp [rst_iso, b2, one_mul, one_pow, sub_eq_add_neg, mul_add, add_mul]
  rw [mul_comm _ (2*s), mul_assoc 2, add_assoc (e.a1*e.a1), ←add_assoc (2*(s*e.a1)),
    ←add_mul, add4, ←neg_mul_right]
  rw [←mul_assoc (2*s), mul_comm _ 2, ←mul_assoc 2, mul4, ←neg_mul_right, mul_assoc 4 s s]
  rw [add_comm (4*(s*e.a1)), add_comm (4*e.a2), add_assoc, add_assoc, add_comm (4*(s*s)), ←add_assoc]
  simp [←add_assoc (4*(s*e.a1))]
  rw [add_assoc, add_assoc, neg_add_self (4*(s*s))]
  ring

open ring_neg in
lemma rst_b4 (r s t : R) (e : Model R) :
  (rst_iso r s t e).b4 = e.b4 + r * (e.b2 + 6 * r) :=
by
  simp only [rst_iso, b2, b4]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, sub_add]
  simp [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm, neg_add_eq_sub, add_sub]
  ring

open ring_neg in
lemma rst_b6 (r s t : R) (e : Model R) :
  (rst_iso r s t e).b6 = e.b6 + 2*r*e.b4 + r*r*e.b2 + 4*r*r*r :=
by
  simp only [rst_iso, b2, b4, b6]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, sub_add]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm, neg_add_eq_sub, add_sub]
  ring

open ring_neg in
lemma rst_b8 (r s t : R) (e : Model R) :
  (rst_iso r s t e).b8 = e.b8 + 3*r*e.b6 + 3*r*r*e.b4 + r*r*r*e.b2 + 3*r*r*r*r :=
by
  simp only [rst_iso, b2, b4, b6, b8, one_mul, one_pow]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm', neg_add_eq_sub, add_sub, sub_add]
  ring

open ring_neg in
lemma rst_discr (r s t : R) (e : Model R) : (rst_iso r s t e).discr = e.discr :=
by
  simp only [discr, rst_b2, rst_b4, rst_b6, rst_b8]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, pow_zero, mul_one, one_mul]
  rw [(by ring : b2 e * (12 * r) * b8 e = b2 e * (3 * r) * (4 * b8 e)),
      (by ring : 12 * r * b2 e * b8 e = 3 * r * b2 e * (4 * b8 e)),
      (by ring : 12 * r * (12 * r) * b8 e = 3 * r * 12 * r * (4 * b8 e))]
  simp only [b8_identity]
  simp only [← sub_add_comm, neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, pow_zero]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm', ← sub_eq_add_neg,
    neg_add_eq_sub, add_sub, ← sub_add]
  ring

def weierstrass (e : Model R) (P : R × R) : R :=
  P.2 ^ 2 + e.a1 * P.1 * P.2 + e.a3 * P.2 - (P.1 ^ 3 + e.a2 * P.1 ^ 2 + e.a4 * P.1 + e.a6)

--partial derivation library?

def dweierstrass_dx (e : Model R) (P : R × R) : R :=
  e.a1 * P.2 - (3 * P.1 ^ 2 + 2 * e.a2 * P.1 + e.a4)

def dweierstrass_dy (e : Model R) (P : R × R) : R :=
  2 * P.2 + e.a1 * P.1 + e.a3


open ring_neg in
/--

We can compute the discriminant in terms of these using `Singular.jl`, part of `OSCAR`

```julia
julia> using Oscar

julia> R, ( x, y, a1, a2, a3, a4, a6 ) = PolynomialRing( ZZ, [ "x", "y", "a1", "a2", "a3", "a4", "a6" ] )
(Singular Polynomial Ring (ZZ),(x,y,a1,a2,a3,a4,a6),(dp(7),C), spoly{n_Z}[x, y, a1, a2, a3, a4, a6])

julia> I = Ideal( R, [2*y + a1*x + a3,y*a1 - (3*x^2 + 2*a2*x + a4), y ^2 + a1*x*y + a3*y - (x^3 + a2*x^2 + a4*x + a6)] )
Singular ideal over Singular Polynomial Ring (ZZ),(x,y,a1,a2,a3,a4,a6),(dp(7),C) with generators (x*a1 + 2*y + a3, -3*x^2 + y*a1 - 2*x*a2 - a4, -x^3 + x*y*a1 - x^2*a2 + y^2 + y*a3 - x*a4 - a6)

julia> IE = eliminate(eliminate(I, x), y)
Singular ideal over Singular Polynomial Ring (ZZ),(x,y,a1,a2,a3,a4,a6),(dp(7),C) with generators (a1^4*a2*a3^2 - a1^5*a3*a4 + a1^6*a6 + 8*a1^2*a2^2*a3^2 - a1^3*a3^3 - 8*a1^3*a2*a3*a4 - a1^4*a4^2 + 12*a1^4*a2*a6 + 16*a2^3*a3^2 - 36*a1*a2*a3^3 - 16*a1*a2^2*a3*a4 + 30*a1^2*a3^2*a4 - 8*a1^2*a2*a4^2 + 48*a1^2*a2^2*a6 - 36*a1^3*a3*a6 + 27*a3^4 - 72*a2*a3^2*a4 - 16*a2^2*a4^2 + 96*a1*a3*a4^2 + 64*a2^3*a6 - 144*a1*a2*a3*a6 - 72*a1^2*a4*a6 + 64*a4^3 + 216*a3^2*a6 - 288*a2*a4*a6 + 432*a6^2)

julia> lift(I, IE)[1][1]
-x^2*a1^5*gen(1)+y*a1^6*gen(1)-x*a1^5*a2*gen(1)-x*y*a1^4*gen(1)-y*a1^5*gen(2)-a1^6*gen(3)-9*x^2*a1^3*a2*gen(1)+x*a1^4*a2*gen(2)+11*y*a1^4*a2*gen(1)-10*x*a1^3*a2^2*gen(1)+x*a1^4*a3*gen(1)+a1^4*a2*a3*gen(1)-a1^5*a4*gen(1)-4*x*y*a1^3*gen(2)-6*y^2*a1^3*gen(1)-8*x*y*a1^2*a2*gen(1)-10*y*a1^3*a2*gen(2)-12*a1^4*a2*gen(3)-24*x^2*a1*a2^2*gen(1)+8*x*a1^2*a2^2*gen(2)+40*y*a1^2*a2^2*gen(1)-32*x*a1*a2^3*gen(1)+30*x^2*a1^2*a3*gen(1)-2*x*a1^3*a3*gen(2)-35*y*a1^3*a3*gen(1)+38*x*a1^2*a2*a3*gen(1)-a1^3*a2*a3*gen(2)+8*a1^2*a2^2*a3*gen(1)-a1^3*a3^2*gen(1)+3*x*a1^3*a4*gen(1)+a1^4*a4*gen(2)-9*a1^3*a2*a4*gen(1)+12*y*a1^3*gen(3)-32*x*y*a1*a2*gen(2)-48*y^2*a1*a2*gen(1)+32*x^2*a2^2*gen(2)+48*x*y*a2^2*gen(1)-32*y*a1*a2^2*gen(2)-48*a1^2*a2^2*gen(3)+32*x*a2^3*gen(2)+32*y*a2^3*gen(1)+24*x*y*a1*a3*gen(1)+28*y*a1^2*a3*gen(2)+36*a1^3*a3*gen(3)+30*x^2*a2*a3*gen(1)-46*x*a1*a2*a3*gen(2)-134*y*a1*a2*a3*gen(1)+76*x*a2^2*a3*gen(1)-8*a1*a2^2*a3*gen(2)+16*a2^3*a3*gen(1)-27*x*a1*a3^2*gen(1)+a1^2*a3^2*gen(2)-36*a1*a2*a3^2*gen(1)+60*x^2*a1*a4*gen(1)-58*y*a1^2*a4*gen(1)+84*x*a1*a2*a4*gen(1)+8*a1^2*a2*a4*gen(2)-24*a1*a2^2*a4*gen(1)+31*a1^2*a3*a4*gen(1)+96*y*a1*a2*gen(3)-96*x*a2^2*gen(3)-64*a2^3*gen(3)+96*x*y*a3*gen(2)+144*y^2*a3*gen(1)+52*y*a2*a3*gen(2)+168*a1*a2*a3*gen(3)+84*x*a3^2*gen(2)+198*y*a3^2*gen(1)+38*a2*a3^2*gen(2)+27*a3^3*gen(1)-96*x^2*a4*gen(2)-144*x*y*a4*gen(1)+56*y*a1*a4*gen(2)+60*a1^2*a4*gen(3)-112*x*a2*a4*gen(2)-120*y*a2*a4*gen(1)+16*a2^2*a4*gen(2)-168*x*a3*a4*gen(1)-36*a1*a3*a4*gen(2)-34*a2*a3*a4*gen(1)+60*a1*a4^2*gen(1)+36*x*a1*a6*gen(1)+12*a1^2*a6*gen(2)+24*a1*a2*a6*gen(1)-288*y*a3*gen(3)-252*a3^2*gen(3)+288*x*a4*gen(3)+240*a2*a4*gen(3)-64*a4^2*gen(2)+144*x*a6*gen(2)+216*y*a6*gen(1)+48*a2*a6*gen(2)-36*a3*a6*gen(1)-432*a6*gen(3)
```
-/
lemma discr_eq_neg_singular (e : Model R) : e.discr = -(
  e.a1^4*e.a2*e.a3^2 - e.a1^5*e.a3*e.a4 + e.a1^6*e.a6 + 8*e.a1^2*e.a2^2*e.a3^2 - e.a1^3*e.a3^3
    - 8*e.a1^3*e.a2*e.a3*e.a4 - e.a1^4*e.a4^2 + 12*e.a1^4*e.a2*e.a6 + 16*e.a2^3*e.a3^2
    - 36*e.a1*e.a2*e.a3^3 - 16*e.a1*e.a2^2*e.a3*e.a4 + 30*e.a1^2*e.a3^2*e.a4 - 8*e.a1^2*e.a2*e.a4^2
    + 48*e.a1^2*e.a2^2*e.a6 - 36*e.a1^3*e.a3*e.a6 + 27*e.a3^4 - 72*e.a2*e.a3^2*e.a4
    - 16*e.a2^2*e.a4^2 + 96*e.a1*e.a3*e.a4^2 + 64*e.a2^3*e.a6 - 144*e.a1*e.a2*e.a3*e.a6
    - 72*e.a1^2*e.a4*e.a6 + 64*e.a4^3 + 216*e.a3^2*e.a6 - 288*e.a2*e.a4*e.a6 + 432*e.a6^2)
 :=
by
  simp only [discr, weierstrass, dweierstrass_dx, dweierstrass_dy, b2, b4, b6, b8]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm', neg_add_eq_sub,
    add_sub, sub_add, ← sub_eq_add_neg]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add]
  ring


open ring_neg in
set_option maxHeartbeats 600000 in
lemma discr_in_jacobian_ideal (e : Model R) (P : R × R) : e.discr =
  -((48*P.1*P.2*e.a2^2 +24*e.a1*e.a2*e.a6 +216*P.2*e.a6 +P.2*e.a1^6 +11*P.2*e.a1^4*e.a2 +P.1*e.a1^4*e.a3 +38*P.1*e.a1^2*e.a2*e.a3 +8*e.a1^2*e.a2^2*e.a3
  +e.a1^4*e.a2*e.a3 +40*P.2*e.a1^2*e.a2^2 +32*P.2*e.a2^3 +24*P.1*P.2*e.a1*e.a3 +30*P.1^2*e.a2*e.a3 +3*P.1*e.a1^3*e.a4 +60*P.1^2*e.a1*e.a4 +30*P.1^2*e.a1^2*e.a3
  +31*e.a1^2*e.a3*e.a4 +144*P.2^2*e.a3 +198*P.2*e.a3^2 +27*e.a3^3 +60*e.a1*e.a4^2 +36*P.1*e.a1*e.a6 +76*P.1*e.a2^2*e.a3 +16*e.a2^3*e.a3 +84*P.1*e.a1*e.a2*e.a4
  -(36*e.a3*e.a6 +P.1^2*e.a1^5 +P.1*e.a1^5*e.a2 +P.1*P.2*e.a1^4 +9*P.1^2*e.a1^3*e.a2 +10*P.1*e.a1^3*e.a2^2 +e.a1^5*e.a4 +6*P.2^2*e.a1^3 +8*P.1*P.2*e.a1^2*e.a2
  +24*P.1^2*e.a1*e.a2^2 +32*P.1*e.a1*e.a2^3 +35*P.2*e.a1^3*e.a3 +e.a1^3*e.a3^2 +9*e.a1^3*e.a2*e.a4 +48*P.2^2*e.a1*e.a2 +134*P.2*e.a1*e.a2*e.a3 +27*P.1*e.a1*e.a3^2 +36*e.a1*e.a2*e.a3^2
  +58*P.2*e.a1^2*e.a4 +24*e.a1*e.a2^2*e.a4 +144*P.1*P.2*e.a4 +120*P.2*e.a2*e.a4 +168*P.1*e.a3*e.a4 +34*e.a2*e.a3*e.a4))*(dweierstrass_dy e P)

  +(e.a1^2*e.a3^2 +12*e.a1^2*e.a6 +16*e.a2^2*e.a4 +32*P.1*e.a2^3 +e.a1^4*e.a4 +144*P.1*e.a6 +48*e.a2*e.a6 +P.1*e.a1^4*e.a2 +84*P.1*e.a3^2 +56*P.2*e.a1*e.a4 +8*e.a1^2*e.a2*e.a4 +28*P.2*e.a1^2*e.a3 +52*P.2*e.a2*e.a3
  +96*P.1*P.2*e.a3 +8*P.1*e.a1^2*e.a2^2 +38*e.a2*e.a3^2 +32*P.1^2*e.a2^2
  -(2*P.1*e.a1^3*e.a3 +112*P.1*e.a2*e.a4 +e.a1^3*e.a2*e.a3 +36*e.a1*e.a3*e.a4 +96*P.1^2*e.a4 +32*P.1*P.2*e.a1*e.a2 +32*P.2*e.a1*e.a2^2 +64*e.a4^2
  +4*P.1*P.2*e.a1^3 +10*P.2*e.a1^3*e.a2 +P.2*e.a1^5 +8*e.a1*e.a2^2*e.a3 +46*P.1*e.a1*e.a2*e.a3))*(dweierstrass_dx e P)

  +(60*e.a1^2*e.a4 +288*P.1*e.a4 +240*e.a2*e.a4 +12*P.2*e.a1^3 +36*e.a1^3*e.a3 +96*P.2*e.a1*e.a2 +168*e.a1*e.a2*e.a3
  -(432*e.a6 +e.a1^6 +288*P.2*e.a3 +252*e.a3^2 +12*e.a1^4*e.a2 +48*e.a1^2*e.a2^2 +96*P.1*e.a2^2 +64*e.a2^3))*(weierstrass e P))
 :=
by
  rw [discr_eq_neg_singular, neg_eq_neg_iff]
  simp only [weierstrass, dweierstrass_dx, dweierstrass_dy]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_sub, sub_mul, pow_zero, mul_one]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add, sub_add_comm', neg_add_eq_sub,
    add_sub, sub_add, ← sub_eq_add_neg]
  simp only [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, sub_neg]
  simp only [sub_add_comm', eq_sub_iff_add_eq, sub_eq_iff_eq_add]
  ring

def var_change (r s t : R) (P' : R × R) : R × R :=
  (P'.1 + r, P'.2 + s * P'.1 + t)

@[simp]
lemma var_change_comp (r s t : R) (r' s' t' : R) (P : R × R) :
  var_change r s t (var_change r' s' t' P) = var_change (r + r') (s + s') (t + t' + s * r') P :=
by
  simp only [var_change, Prod.mk.injEq]
  apply And.intro -- TODO look up syntax for apply to both subgoals
  . ring
  . ring

@[simp]
lemma var_change_zero (P : R × R) : var_change (0 : R) 0 0 P = P :=
by simp [var_change]

-- TODO probably these proofs should be more conceptual

open ring_neg in
theorem weierstrass_iso_eq_var_change (e : Model R) (P : R × R) :
  weierstrass (rst_iso r s t e) P = weierstrass e (var_change r s t P) :=
by
  simp only [weierstrass, rst_iso, var_change]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add, neg_add_eq_sub, add_sub, sub_add]
  ring

-- TODO generalize to include s ne 0
open ring_neg in
theorem dweierstrass_dx_iso_eq_var_change (e : Model R) (P : R × R) :
  dweierstrass_dx (rst_iso r 0 t e) P = dweierstrass_dx e (var_change r 0 t P) :=
by
  simp only [dweierstrass_dx, rst_iso, var_change]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, pow_zero, mul_one]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add, neg_add_eq_sub, add_sub, sub_add]
  ring

open ring_neg in
theorem dweierstrass_dy_iso_eq_var_change (e : Model R) (P : R × R) :
  dweierstrass_dy (rst_iso r s t e) P = dweierstrass_dy e (var_change r s t P) :=
by
  simp only [dweierstrass_dy, rst_iso, var_change]
  -- this is a hacky way to get a version of ring with negs, we expand everything and move
  -- the negatives to the other side, to get a purely additive expression
  simp only [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
    ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, pow_zero, mul_one]
  simp only [eq_sub_iff_add_eq, sub_eq_iff_eq_add, neg_add_eq_sub, add_sub, sub_add]
  ring

def rst_triple (e : Model R) (rst : R × R × R) : Model R :=
  rst_iso rst.fst rst.snd.fst rst.snd.snd e

lemma rst_iso_to_triple (e : Model R) (r s t : R) : rst_iso r s t e = rst_triple e (r, s, t) := rfl

end Model

structure ValidModel (R : Type u) [IntegralDomain R] extends Model R where
  discr_not_zero : toModel.discr ≠ 0

namespace ValidModel
variable {R : Type u} [IntegralDomain R]
instance [Repr R] : Repr (ValidModel R) := ⟨ λ (e : ValidModel R) _ => repr e.toModel⟩

def rst_iso (r s t : R) (e : ValidModel R) : ValidModel R := {
  toModel := Model.rst_iso r s t e.toModel,
  discr_not_zero := by
    rw [Model.rst_discr]
    exact e.discr_not_zero }

@[simp]
lemma rst_discr_valid (r s t : R) (e : ValidModel R) : (rst_iso r s t e).discr = e.discr :=
  Model.rst_discr r s t e.toModel

--more [simp] lemmas
@[simp]
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
  mul_zero, one_mul, add_zero, mul_assoc, pow_two r, pow_succ r, pow_zero, mul_one]

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
  add_zero, mul_assoc, ←pow_two t, zero_mul, mul_add, sub_sub]

lemma st_of_b8 (e : ValidModel R) (s t : R) : (rst_iso 0 s t e).b8 = e.b8 := by
  rw [rst_iso, Model.rst_b8]
  simp only [mul_zero, add_zero, zero_mul]

def rst_triple (e : ValidModel R) (rst : R × R × R) : ValidModel R :=
  rst_iso rst.fst rst.snd.fst rst.snd.snd e

lemma rst_iso_to_triple (e : ValidModel R) (r s t : R) : rst_iso r s t e = rst_triple e (r, s, t) :=
rfl

end ValidModel


namespace Model

namespace Field
variable {K : Type u} [Field K]

def is_singular_point (e : Model K) (P : K × K) : Prop :=
weierstrass e P = 0 ∧ dweierstrass_dx e P = 0 ∧ dweierstrass_dy e P = 0

lemma discr_eq_zero_of_singular (e : Model K) {P} (h : is_singular_point e P) :
  e.discr = 0 :=
by
  rcases h with ⟨h₁, h₂, h₃⟩
  rw [discr_in_jacobian_ideal, h₁, h₂, h₃, mul_zero,
    mul_zero, mul_zero, add_zero, add_zero, neg_eq_zero]

open Classical PerfectRing

/--
Proposition 1.5.4 of Elliptic Curve Handbook, Ian Connell February, 1999,
https://www.math.rug.nl/~top/ian.pdf
-/
noncomputable
def singular_point [PerfectRing K] (e : Model K) : K × K :=
  if e.c4 = 0 then
    match ring_char K with
    | 2 => (pth_root e.a4, pth_root (e.a2 * e.a4 + e.a6))
    | 3 => (pth_root (-e.a3 ^ 2 - e.a6), e.a1 * pth_root (-e.a3 ^ 2 - e.a6) + e.a3)
    | _ => (e.b2 / 12, -(e.a1 * e.b2 / 12 + e.a3) / 2)
  else
    ((18 * e.b6 - e.b2 * e.b4) / e.c4, (e.b2 * e.b5 + 3 * e.b7) / e.c4)

section invariant_lemmas

lemma c4_zero_iff_a1_zero_of_char_two (e : Model K) (h : ring_char K = 2) :
  e.c4 = 0 ↔ e.a1 = 0 :=
by
  have hchar' : (ring_char K : K) = 2 := by simp [h]
  have hchar'' : (2 : K) = 0 := by simp [← hchar', ring_char_eq_zero]
  rw [c4, b2, show 24 = 2 * 12 by norm_num, show 4 = 2 * 2 by norm_num, hchar'', ← pow_two]
  simp only [mul_zero, zero_mul, add_zero, ← pow_mul, sub_zero] -- TODO simp? doesn't do back arrows
  rw [pow_eq_zero_iff]
  norm_num

lemma c4_zero_iff_b2_zero_of_char_three (e : Model K) (h : ring_char K = 3) :
  e.c4 = 0 ↔ e.b2 = 0 :=
by
  have hchar' : (ring_char K : K) = 3 := by simp [h]
  have hchar'' : (3 : K) = 0 := by simp [← hchar', ring_char_eq_zero]
  rw [c4, show 24 = 3 * 8 by norm_num, hchar'']
  simp only [mul_zero, zero_mul, add_zero, sub_zero] -- TODO simp? doesn't do back arrows
  rw [pow_eq_zero_iff]
  norm_num

-- TODO is this actually an iff
lemma a3_zero_of_a1_zero_of_disc_zero_of_char_two
  (e : Model K) (h : ring_char K = 2) (hdisc : e.discr = 0) (ha1 : e.a1 = 0) :
  e.a3 = 0 :=
by
  have hchar' : (ring_char K : K) = 2 := by simp [h]
  have hchar'' : (2 : K) = 0 := by simp [← hchar', ring_char_eq_zero]
  rw [discr, b2, b4, b6, b8, ha1,
    show 8 = 2 * 4 by norm_num, show 4 = 2 * 2 by norm_num, show 27 = 2 * 13 + 1 by norm_num, hchar''] at hdisc
  -- TODO simp identifier "at" can't be on next line
  simp only [mul_zero, zero_mul, add_zero, neg_zero, sub_self, zero_add, one_mul, zero_sub, neg_eq_zero] at hdisc
  rw [← pow_two, ← pow_two, ← pow_mul] at hdisc
  rwa [pow_eq_zero_iff] at hdisc
  norm_num

-- TODO is this actually an iff discr
lemma b4_zero_of_b2_zero_of_disc_zero_of_char_three
  (e : Model K) (h : ring_char K = 3) (hdisc : e.discr = 0) (hb2 : e.b2 = 0) :
  e.b4 = 0 :=
by
  have hchar' : (ring_char K : K) = 3 := by simp [h]
  have hchar'' : (3 : K) = 0 := by simp [← hchar', ring_char_eq_zero]
  rw [discr, hb2,
    show 27 = 3 * 9 by norm_num,
    show 8 = 3 * 3 - 1 by norm_num,
    hchar''] at hdisc
  -- TODO simp identifier "at" can't be on next line
  simp at hdisc
  rw [← neg_mul_left, one_mul, neg_eq_zero] at hdisc
  rwa [pow_eq_zero_iff] at hdisc
  norm_num

end invariant_lemmas

-- TODO maybe rewrite to take an explicit point
open ring_neg in
lemma is_singular_point_singular_point [PerfectRing K] (e : Model K) (h : e.discr = 0) :
  is_singular_point e (singular_point e) :=
by
  rw [singular_point]
  split_ifs with hc4 hc4
  . split
    . rw [is_singular_point]
      have hchar : ring_char K = 2 := by assumption
      have hchar' : (ring_char K : K) = 2 := by simp [hchar]
      have hchar'' : (2 : K) = 0 := by simp [← hchar', ring_char_eq_zero]
      have hcharne : ring_char K ≠ 0 := by simp [hchar]
      have ha1 : e.a1 = 0 := by simpa [c4_zero_iff_a1_zero_of_char_two e hchar] using hc4
      have ha3 : e.a3 = 0 := a3_zero_of_a1_zero_of_disc_zero_of_char_two e hchar h ha1
      refine ⟨?_, ?_, ?_⟩
      . rw [weierstrass]
        simp only [ha1, ha3, mul_zero, zero_add, zero_mul, add_zero]
        rw [show 3 = 2 + 1 by norm_num]
        rw [pow_succ _ 2]
        rw [← hchar, pth_root_pow_char hcharne]
        rw [pth_root_pow_char hcharne]
        simp only [add_sub_add_right_eq_sub, sub_eq_iff_eq_add, zero_add]
        rw [show pth_root e.a4 * e.a4 + e.a2 * e.a4 + e.a4 * pth_root e.a4 =
                2 * (pth_root e.a4 * e.a4) + e.a2 * e.a4 by ring]
        rw [hchar'', zero_mul, zero_add]
      . rw [dweierstrass_dx]
        simp only [ha1, zero_mul, hchar'', add_zero, zero_sub, neg_add_rev]
        rw [← hchar, pth_root_pow_char hcharne, ← sub_eq_add_neg]
        simp only [add_sub_add_right_eq_sub, sub_eq_iff_eq_add, zero_add]
        rw [show (3 : K) = 2 * 2 - 1 by norm_num]
        rw [hchar'']
        simp [← neg_mul_left]
      . simp [dweierstrass_dy, ha1, ha3, hchar'']
    . rw [is_singular_point]
      have hchar : ring_char K = 3 := by assumption
      have hcharne : ring_char K ≠ 0 := by simp [hchar]
      have hchar' : (ring_char K : K) = 3 := by simp [hchar]
      have hchar'' : (3 : K) = 0 := by simp [← hchar', ring_char_eq_zero]
      have hb2 : e.b2 = 0 := by simpa [c4_zero_iff_b2_zero_of_char_three e hchar] using hc4
      have hb4 : e.b4 = 0 := b4_zero_of_b2_zero_of_disc_zero_of_char_three e hchar h hb2
      refine ⟨?_, ?_, ?_⟩
      . rw [weierstrass]
        simp
        rw [← hchar, pth_root_pow_char hcharne]
        simp
        simp [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
          ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, pow_zero, mul_one]
        simp [eq_sub_iff_add_eq, sub_eq_iff_eq_add, neg_add_eq_sub, add_sub, sub_add]
        sorry
      . rw [dweierstrass_dx]
        simp
        rw [hchar'', zero_mul, zero_add]
        simp [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
          ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, pow_zero, mul_one]
        simp [eq_sub_iff_add_eq, sub_eq_iff_eq_add, neg_add_eq_sub, add_sub, sub_add]
        sorry
      . rw [dweierstrass_dy]
        simp [sub_add_comm', neg_pow_three, neg_add_eq_sub, sub_sub, pow_succ, ← neg_mul_left,
          ← neg_mul_right, mul_add, add_mul, mul_sub, sub_mul, pow_zero, mul_one]
        simp [eq_sub_iff_add_eq, sub_eq_iff_eq_add, neg_add_eq_sub, add_sub, sub_add]
        rw [show 2 * (e.a1 * pth_root (e.a3 * e.a3 - e.a6)) + 2 * e.a3
            + e.a1 * pth_root (e.a3 * e.a3 - e.a6) + e.a3 = 3 * ((e.a1 * pth_root (e.a3 * e.a3 - e.a6)) + e.a3) by ring]
        rw [hchar'', zero_mul]
    . rw [is_singular_point]
      refine ⟨?_, ?_, ?_⟩
      . rw [weierstrass]
        simp
        sorry
      . rw [dweierstrass_dx]
        sorry
      . rw [dweierstrass_dy]
        sorry
  . rw [is_singular_point]
    refine ⟨?_, ?_, ?_⟩
    . rw [weierstrass]
      simp
      sorry
    . rw [dweierstrass_dx]
      sorry
    . rw [dweierstrass_dy]
      sorry


/--
Proposition 1.5.4 of Elliptic Curve Handbook, Ian Connell February, 1999,
https://www.math.rug.nl/~top/ian.pdf
-/
noncomputable
def move_singular_point_to_origin_triple [PerfectRing K] (e : Model K) : K × K × K :=
⟨(singular_point e).1, 0, (singular_point e).2⟩

noncomputable
def move_singular_point_to_origin_iso [PerfectRing K] (e : Model K) : Model K :=
rst_triple e (move_singular_point_to_origin_triple e)

lemma move_singular_point (e : Model K) (r t : K) {P : K × K} (h : is_singular_point e P) :
  is_singular_point (rst_iso r 0 t e) (var_change (-r) 0 (-t) P) :=
by
  rw [is_singular_point, weierstrass_iso_eq_var_change,
    dweierstrass_dx_iso_eq_var_change, dweierstrass_dy_iso_eq_var_change, var_change_comp]
  simpa

lemma move_singular_point_to_origin [PerfectRing K] (e : Model K) (h : e.discr = 0) :
  is_singular_point (move_singular_point_to_origin_iso e) (0, 0) :=
by
  rw [move_singular_point_to_origin_iso, rst_triple, move_singular_point_to_origin_triple]
  convert move_singular_point e (singular_point e).fst (singular_point e).snd
    (is_singular_point_singular_point e h)
  . simp [var_change]
  . simp [var_change]

lemma move_singular_point_to_origin' [PerfectRing K] (e : Model K) :
  (∃ P, is_singular_point e P) →
    is_singular_point (move_singular_point_to_origin_iso e) (0, 0) := by sorry

end Field

end Model
