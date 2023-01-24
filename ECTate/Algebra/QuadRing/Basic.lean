import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Rat.Order

-- manual port of https://github.com/alexjbest/diophantine-toolkit/blob/master/src/number_theory/QuadRing/basic.lean

/-- `QuadRing F a b` adjoins a root `α` of `x^2 - ax - b` to the ring (field) `F`.
For example, `ℤ[√5]` can be defined as `QuadRing ℤ 0 5`.
Elements of `QuadRing` are represented as a pair `⟨b1, b2⟩` standing for the element `b1 + b2 α`.
-/
@[ext]
structure QuadRing (F : Type _) (a b : F) :=
(b1 b2 : F)
deriving Repr

-- attribute [pp_using_anonymous_constructor] QuadRing

namespace QuadRing

section

variable (F : Type _) (a b : F)

@[simp] theorem eta : ∀ z : QuadRing F a b, (⟨z.b1,z.b2⟩ : QuadRing F a b) = z
| ⟨_,_⟩ => rfl

/-!
### Basic constructions of elements in `QuadRing R a b`
-/

/-- The standard inclusion `F → QuadRing F a b`. -/
instance [Zero F] : Coe F (QuadRing F a b) := ⟨λ r => ⟨r, 0⟩⟩

@[simp] lemma coe_b1 [Zero F] (r : F) : (r : QuadRing F a b).b1 = r := rfl

@[simp] lemma coe_b2 [Zero F] (r : F) : (r : QuadRing F a b).b2 = 0 := rfl

@[simp] theorem coe_inj [Zero F] {z w : F} : (z : QuadRing F a b) = w ↔ z = w :=
⟨congr_arg b1, by aesop⟩

-- lemma coe_injective [Zero F] : Function.Injective (coe : F → QuadRing F a b) :=
-- λ a b => (coe_inj F a b).mp

/-- `QuadRing.root F a b` is the adjoined root `α` of the polynomial `x^2 - ax - b`. -/
def root [Zero F] [One F] : QuadRing F a b := ⟨0, 1⟩

@[simp] lemma root_b1 [Zero F] [One F]: (root F a b).b1 = 0 := rfl
@[simp] lemma root_b2 [Zero F] [One F]: (root F a b).b2 = 1 := rfl

variables [CommRing F]
/-!
### Ring stucture on `QuadRing R a b`
-/

instance : Zero (QuadRing F a b) := ⟨(0 : F)⟩
instance : Inhabited (QuadRing F a b) := ⟨0⟩

@[simp] lemma zero_b1 : (0 : QuadRing F a b).b1 = 0 := rfl
@[simp] lemma zero_b2 : (0 : QuadRing F a b).b2 = 0 := rfl

@[simp] lemma coe_zero : ((0 : F) : QuadRing F a b) = 0 := rfl

@[simp] theorem coe_eq_zero {z : F} : (z : QuadRing F a b) = 0 ↔ z = 0 :=
coe_inj F a b

instance : One (QuadRing F a b) := ⟨(1 : F)⟩

@[simp] lemma one_b1 : (1 : QuadRing F a b).b1 = 1 := rfl
@[simp] lemma one_b2 : (1 : QuadRing F a b).b2 = 0 := rfl

@[simp] lemma coe_one : ((1 : F) : QuadRing F a b) = 1 := rfl

instance : Add (QuadRing F a b) := ⟨λ z w => ⟨z.b1 + w.b1, z.b2 + w.b2⟩⟩

@[simp] lemma add_b1 (z w : QuadRing F a b) : (z + w).b1 = z.b1 + w.b1 := rfl
@[simp] lemma add_b2 (z w : QuadRing F a b) : (z + w).b2 = z.b2 + w.b2 := rfl

@[simp] lemma coe_add (r s : F) : ((r + s : F) : QuadRing F a b) = r + s :=
(QuadRing.ext_iff _ _).2 $ by simp

instance : Neg (QuadRing F a b) := ⟨λ z => ⟨-z.b1, -z.b2⟩⟩

@[simp] lemma neg_b1 (z : QuadRing F a b) : (-z).b1 = -z.b1 := rfl
@[simp] lemma neg_b2 (z : QuadRing F a b) : (-z).b2 = -z.b2 := rfl

@[simp] lemma coe_neg (n : F) : (↑(-n) : QuadRing F a b) = - ↑n := by ext; simp; sorry

instance : Sub (QuadRing F a b) := ⟨λ z w => ⟨z.b1 - w.b1, z.b2 - w.b2⟩⟩

@[simp] lemma sub_b1 (z w : QuadRing F a b) : (z - w).b1 = z.b1 - w.b1 := rfl
@[simp] lemma sub_b2 (z w : QuadRing F a b) : (z - w).b2 = z.b2 - w.b2 := rfl

@[simp] lemma coe_sub (z w : F) : (↑(z - w) : QuadRing F a b) = ↑z - ↑w := by ext; simp; sorry

/-- This scalar multiplication is used to define `nsmul`, `zsmul` and `qsmul`. -/
instance {R F : Type _} [SMul R F] (a b : F) : SMul R (QuadRing F a b) :=
{ smul := λ c x => ⟨c • x.b1, c • x.b2⟩ }

@[simp] lemma smul_b1 {R F : Type _} [SMul R F] {a b : F} (c : R) (z : QuadRing F a b) :
  (c • z).b1 = c • z.b1 := rfl
@[simp] lemma smul_b2 {R F : Type _} [SMul R F] {a b : F} (c : R) (z : QuadRing F a b) :
  (c • z).b2 = c • z.b2 := rfl

/-! We want to define the `CommRing (QuadRing F a b)` instance in multiple steps,
so we can insert the right operations on `ℕ`, `ℤ` (and `ℚ`).
These operations have to be defined in the right way to ensure all diamond instances
involving e.g. `QuadRing ℤ a b` are indeed definitionally equal.
-/

instance : AddCommMonoidWithOne (QuadRing F a b) :=
{ add := (. + .)
  zero := (0)
  one := (1)
  add_assoc := by intros; ext <;> apply add_assoc
  add_comm := by intros; ext <;> apply add_comm
  zero_add := by intros; ext <;> apply zero_add
  add_zero := by intros; ext <;> apply add_zero
  nsmul := (.•.),
  nsmul_zero := by intros; ext <;> apply zero_nsmul
  nsmul_succ := by intros; ext <;> apply succ_nsmul
  natCast := λ n => ↑(n : F)
  natCast_zero := by simp
  natCast_succ := by intros; simp }


@[simp] lemma coe_coe_nat (n : ℕ) : ((n : F) : QuadRing F a b) = n := rfl

instance : AddCommGroup (QuadRing F a b) :=
{ instAddCommMonoidWithOneQuadRing F a b with
  add_left_neg := by intros; ext <;> apply add_left_neg,
  sub := Sub.sub
  zsmul := (.•.)
  zsmul_zero' := by intros; ext <;> apply zero_zsmul
  zsmul_succ' := sorry --by intros; ext <;> simp [add_mul, zsmul_succ', add_comm]
  zsmul_neg' := sorry --by intros; ext <;> simp [add_mul]
  sub_eq_add_neg := by intros; ext <;> apply sub_eq_add_neg }

instance : AddCommGroupWithOne (QuadRing F a b) :=
{ instAddCommMonoidWithOneQuadRing F a b,
  instAddCommGroupQuadRing F a b with
  natCast := λ n => ↑(n : F)
  intCast := λ n => ↑(n : F)
  intCast_ofNat := by intros; simp
  intCast_negSucc := by intros; simp [-neg_add_rev, neg_add, ← sub_eq_add_neg] }

@[simp] lemma coe_coe_int (n : ℤ) : ((n : F) : QuadRing F a b) = n := rfl

@[simp] lemma coe_nat_b1 (n : ℕ) : (n : QuadRing F a b).b1 = n := rfl
@[simp] lemma coe_nat_b2 (n : ℕ) : (n : QuadRing F a b).b2 = 0 := rfl

@[simp] lemma coe_nat_add (r s : ℕ) : (↑(r + s) : QuadRing F a b) = r + s :=
by ext <;> simp only [coe_nat_b1, coe_nat_b2, add_b1, add_b2, Nat.cast_add, add_zero]

@[simp] lemma coe_int_b1 (n : ℤ) : (n : QuadRing F a b).b1 = n := rfl
@[simp] lemma coe_int_b2 (n : ℤ) : (n : QuadRing F a b).b2 = 0 := rfl

-- This used to be a non-defeq diamond, we solve this by supplying a custom value for
-- `add_group_with_one.int_cast`
-- example (a b : ℤ) (n) :
--   @@coe (@@coe_to_lift (QuadRing.CoeT ℤ a b)) n = @@coe (@@coe_to_lift int.cast_coe) n :=
-- rfl

@[simp] lemma coe_int_add (r s : ℤ) : (↑(r + s) : QuadRing F a b) = r + s :=
by ext <;> simp only [coe_int_b1, coe_int_b2, add_b1, add_b2, Int.cast_add, add_zero]

instance : Mul (QuadRing F a b) :=
⟨λ z w => ⟨z.1 * w.1 + z.2 * w.2 * b ,z.2 * w.1 + z.1 * w.2 + z.2 * w.2 * a⟩⟩

@[simp] lemma mul_b1 (z w : QuadRing F a b) :
  (z * w).b1 = z.1 * w.1 + z.2 * w.2 * b := rfl
@[simp] lemma mul_b2 (z w : QuadRing F a b) :
  (z * w).b2 = z.2 * w.1 + z.1 * w.2 + z.2 * w.2 * a := rfl

@[simp] lemma coe_mul (r s : F) : ((r * s : F) : QuadRing F a b) = r * s :=
by apply (QuadRing.ext_iff _ _).2; simp [mul_comm]

instance : CommSemiring (QuadRing F a b) :=
{ instAddCommMonoidWithOneQuadRing F a b with
  zero := (0 : QuadRing F a b)
  add := (.+.)
  one := 1
  mul := (.*.)
  nsmul := (.•.)
  npow := npowRec
  mul_comm := by sorry
  mul_one := by sorry
  one_mul := by sorry
  mul_assoc:= by sorry
  mul_zero := by sorry
  zero_mul := by sorry
  right_distrib := by sorry
  left_distrib := by sorry
  }

instance : CommRing (QuadRing F a b) :=
{ instAddCommGroupWithOneQuadRing F a b,
  instCommSemiringQuadRing F a b with
  zero := (0 : QuadRing F a b)
  add := (.+.)
  neg := Neg.neg
  sub := Sub.sub
  one := 1,
  mul := (.*.)
  nsmul := (.•.)
  npow := npowRec
  natCast := λ n => n
  zsmul := (.•.)
  intCast := λ n => n }

instance [Nontrivial F] : Nontrivial (QuadRing F a b) :=
⟨⟨0, 1, by simp [QuadRing.ext_iff]⟩⟩

-- instance [CharZero F] : char_zero (QuadRing F a b) :=
-- ⟨(coe_injective F a b).comp nat.cast_injective⟩

-- @[simp] lemma coe_pow (x : F) : ∀ (n : ℕ), (↑(x ^ n) : QuadRing F a b) = x ^ n
-- | 0 => by simp
-- | (n + 1) = by rw [pow_succ, coe_mul, coe_pow n, pow_succ]

#eval ((⟨1,2⟩ : QuadRing ℚ 0 5) ^2 : QuadRing ℚ 0 5)
