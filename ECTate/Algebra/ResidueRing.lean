import ECTate.Algebra.ValuedRing
import ECTate.FieldTheory.PerfectClosure
import Mathlib.RingTheory.Congruence

open Enat

variable {R : Type u} [CommRing R] [IsDomain R]
section residue

def congruence_p {p : R} (nav : SurjVal p) (a b : R) : Prop := nav (a - b) > 0


variable {p : R}
variable {nav : SurjVal p}

lemma congruence_p_refl : ∀ x : R, congruence_p nav x x := by
  simp [congruence_p]

lemma congruence_p_symm : ∀ {x y : R}, congruence_p nav x y → congruence_p nav y x := by
  simp only [congruence_p, gt_iff_lt]
  intro x y H
  rwa [←neg_neg (y-x), neg_sub, val_neg]

lemma congruence_p_trans : ∀ {x y z : R},
  congruence_p nav x y → congruence_p nav y z → congruence_p nav x z := by
  simp only [congruence_p, gt_iff_lt]
  intro x y z Hxy Hyz
  rw [←add_zero x, ←sub_self (-y), sub_eq_add_neg, sub_eq_add_neg, neg_neg, ←add_assoc,
    ←sub_eq_add_neg x, add_assoc, ←sub_eq_add_neg]
  exact lt_of_lt_of_le (lt_min Hxy Hyz) (nav.v_add_ge_min_v (x-y) (y-z))

lemma eqv_congr : Equivalence (congruence_p nav) :=
{ refl          := congruence_p_refl
  symm          := congruence_p_symm
  trans         := congruence_p_trans }

def equiv_p (nav : SurjVal p) : HasEquiv R :=
{ Equiv := congruence_p nav }

def SurjVal.s (nav : SurjVal p) : Setoid R :=
{ r := congruence_p nav
  iseqv := eqv_congr }

lemma SurjVal.s.r_eq : nav.s.r = congruence_p nav := rfl


--def SurjVal.qt (nav : SurjVal p) := Quotient (val_setoid nav)

notation "⟦" arg1:60 "⟧." arg2:120 => Quotient.mk (SurjVal.s arg2) arg1

theorem add_repr_eq_repr_add (nav : SurjVal p) (a b : R)
  (a' b' : R) (ha : nav.s.r a' a) (hb : nav.s.r b' b) : nav.s.r (a' + b') (a + b) := by
  rw [SurjVal.s.r_eq] at *
  rw [congruence_p, add_sub_assoc, sub_eq_add_neg, neg_add, ←add_assoc b', add_comm _ (-a),
    ←add_assoc, ←add_assoc, add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg]
  exact lt_of_lt_of_le (lt_min ha hb) (SurjVal.v_add_ge_min_v nav (a' - a) (b' - b))

theorem equiv_of_congr (nav : SurjVal p) (a b : R) : nav.s.r a b → (equiv_p nav).Equiv a b := id

def add_quot' (a b : R) : Quotient nav.s := ⟦a + b⟧

def add_quot : Quotient nav.s → Quotient nav.s → Quotient nav.s :=
  Quotient.lift₂ add_quot' fun a b a' b' ha hb =>
  Quotient.sound (equiv_of_congr nav (a + b) (a' + b') (add_repr_eq_repr_add nav a' b' a b ha hb))

instance : Add (Quotient nav.s) :=
{ add := add_quot }

theorem add_quot_eq_quot_add_rep {a b : R} {x y : Quotient nav.s} (hx : ⟦a⟧ = x) (hy : ⟦b⟧ = y) :
  x + y = ⟦a + b⟧ := by
  rw [←hx, ←hy]
  rfl

lemma add_quot_eq_quot_add {a b : R} : ⟦a + b⟧ = ⟦a⟧.nav + ⟦b⟧ := rfl

lemma add_quot_assoc (a b c : Quotient nav.s) : a + b + c = a + (b + c) := by
  match Quotient.exists_rep a, Quotient.exists_rep b, Quotient.exists_rep c with
  | ⟨ra, ha⟩, ⟨rb, hb⟩, ⟨rc, hc⟩ =>
    rw [add_quot_eq_quot_add_rep ha hb, add_quot_eq_quot_add_rep hb hc, add_quot_eq_quot_add_rep ha rfl, add_quot_eq_quot_add_rep rfl hc, add_assoc]

instance : Zero (Quotient nav.s) :=
{ zero := ⟦0⟧ }

lemma quot_zero : (0 : Quotient nav.s) = ⟦0⟧ := rfl

lemma zero_add_quot (a : Quotient nav.s) : 0 + a = a := by
  match Quotient.exists_rep a with
  | ⟨ra, ha⟩ =>
    rw [quot_zero, add_quot_eq_quot_add_rep rfl ha, zero_add, ha]

lemma add_quot_zero (a : Quotient nav.s) : a + 0 = a := by
  match Quotient.exists_rep a with
  | ⟨ra, ha⟩ =>
    rw [quot_zero, add_quot_eq_quot_add_rep ha rfl, add_zero, ha]

lemma add_quot_comm (a b : Quotient nav.s) : a + b = b + a := by
  match Quotient.exists_rep a, Quotient.exists_rep b with
  | ⟨ra, ha⟩, ⟨rb, hb⟩ =>
    rw [add_quot_eq_quot_add_rep ha hb, add_quot_eq_quot_add_rep hb ha, add_comm]

theorem mul_repr_eq_repr_mul (nav : SurjVal p) (a b : R) (a' b' : R) (ha : nav.s.r a' a) (hb : nav.s.r b' b) :
  nav.s.r (a' * b') (a * b) := by
  rw [SurjVal.s.r_eq] at *
  rw [congruence_p] at *
  sorry
  -- have h₁ : nav.v b' + nav.v (a' - a) > nav.v b' + 0
  -- . apply add_lt_add_left ha
  -- simp at h₁
  -- rw [congruence_p, mul_sub_assoc, sub_eq_mul_neg, neg_mul, ←mul_assoc b', mul_comm _ (-a),
  --   ←add_assoc, ←add_assoc, add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg]
  -- exact lt_of_lt_of_le (lt_min ha hb) (SurjVal.v_add_ge_min_v nav (a' - a) (b' - b))

def mul_quot' (a b : R) : Quotient nav.s := ⟦a * b⟧

def mul_quot : Quotient nav.s → Quotient nav.s → Quotient nav.s :=
Quotient.lift₂ mul_quot' fun a b a' b' ha hb =>
  Quotient.sound (equiv_of_congr nav (a * b) (a' * b') (mul_repr_eq_repr_mul nav a' b' a b ha hb))

instance : Mul (Quotient nav.s) :=
{ mul := mul_quot }

theorem mul_quot_eq_quot_mul_rep {a b : R} {x y : Quotient nav.s} (hx : ⟦a⟧ = x) (hy : ⟦b⟧ = y) : x * y = ⟦a * b⟧ := by
  rw [←hx, ←hy]
  rfl

lemma mul_quot_eq_quot_mul {a b : R} : ⟦a * b⟧ = ⟦a⟧.nav * ⟦b⟧ := rfl

lemma left_distrib_quot (a b c : Quotient nav.s) : a * (b + c) = a * b + a * c := by
  match Quotient.exists_rep a, Quotient.exists_rep b, Quotient.exists_rep c with
  | ⟨ra, ha⟩, ⟨rb, hb⟩, ⟨rc, hc⟩ =>
    rw [add_quot_eq_quot_add_rep hb hc, mul_quot_eq_quot_mul_rep ha hb, mul_quot_eq_quot_mul_rep ha hc,
      mul_quot_eq_quot_mul_rep ha rfl, add_quot_eq_quot_add_rep rfl rfl, left_distrib]

lemma right_distrib_quot (a b c : Quotient nav.s) : (a + b) * c = a * c + b * c := by
  match Quotient.exists_rep a, Quotient.exists_rep b, Quotient.exists_rep c with
  | ⟨ra, ha⟩, ⟨rb, hb⟩, ⟨rc, hc⟩ =>
    rw [add_quot_eq_quot_add_rep ha hb, mul_quot_eq_quot_mul_rep ha hc, mul_quot_eq_quot_mul_rep hb hc,
      mul_quot_eq_quot_mul_rep rfl hc, add_quot_eq_quot_add_rep rfl rfl, right_distrib]

lemma zero_mul_quot (a : Quotient nav.s) : 0 * a = 0 := by
  match Quotient.exists_rep a with
  | ⟨ra, ha⟩ =>
    rw [quot_zero, mul_quot_eq_quot_mul_rep rfl ha, zero_mul]

lemma mul_quot_zero (a : Quotient nav.s) : a * 0 = 0 := by
  match Quotient.exists_rep a with
  | ⟨ra, ha⟩ =>
    rw [quot_zero, mul_quot_eq_quot_mul_rep ha rfl, mul_zero]

lemma mul_quot_assoc (a b c : Quotient nav.s) : a * b * c = a * (b * c) := by
  match Quotient.exists_rep a, Quotient.exists_rep b, Quotient.exists_rep c with
  | ⟨ra, ha⟩, ⟨rb, hb⟩, ⟨rc, hc⟩ =>
    rw [mul_quot_eq_quot_mul_rep ha hb, mul_quot_eq_quot_mul_rep hb hc, mul_quot_eq_quot_mul_rep ha rfl,
      mul_quot_eq_quot_mul_rep rfl hc, mul_assoc]

instance : One (Quotient nav.s) :=
{ one := ⟦1⟧ }

lemma quot_one : (1 : Quotient nav.s) = ⟦1⟧ := rfl

lemma one_mul_quot (a : Quotient nav.s) : 1 * a = a := by
  match Quotient.exists_rep a with
  | ⟨ra, ha⟩ =>
    rw [quot_one, mul_quot_eq_quot_mul_rep rfl ha, one_mul, ha]

lemma mul_quot_one (a : Quotient nav.s) : a * 1 = a := by
  match Quotient.exists_rep a with
  | ⟨ra, ha⟩ =>
    rw [quot_one, mul_quot_eq_quot_mul_rep ha rfl, mul_one, ha]

theorem neg_repr_eq_repr_neg (nav : SurjVal p) (a : R) : ∀ (a' : R), nav.s.r a' a → nav.s.r (-a') (-a) := by
  intro a' ha
  rw [SurjVal.s.r_eq] at *
  rwa [congruence_p, ←val_neg, sub_eq_add_neg, neg_neg, neg_add, neg_neg, ←sub_eq_add_neg]

def neg_quot' (a : R) : Quotient nav.s := ⟦-a⟧

def neg_quot : Quotient nav.s → Quotient nav.s := by
  apply Quotient.lift (neg_quot') _
  intro a a' ha
  rw [neg_quot']
  apply Quotient.sound
  apply equiv_of_congr nav _ _ (neg_repr_eq_repr_neg nav a' a ha)

instance : Neg (Quotient nav.s) :=
{ neg := neg_quot }

theorem neg_quot_eq_quot_neg_rep {a : R} {x : Quotient nav.s} (hx : ⟦a⟧ = x) : -x = ⟦-a⟧ := by
  rw [←hx]
  rfl

theorem neg_quot_eq_quot_neg {a : R} : -⟦a⟧.nav = ⟦-a⟧ := rfl

lemma add_left_neg_quot (a : Quotient nav.s) : -a + a = 0 := by
  match Quotient.exists_rep a with
  | ⟨ra, ha⟩ =>
    rw [neg_quot_eq_quot_neg_rep ha, ←ha, add_quot_eq_quot_add_rep rfl rfl, add_left_neg]
    rfl

instance res_ring_p : Ring (Quotient nav.s) :=
{ add_assoc := add_quot_assoc
  zero_add := zero_add_quot
  add_zero := add_quot_zero
  add_comm := add_quot_comm
  left_distrib := left_distrib_quot
  right_distrib := right_distrib_quot
  zero_mul := zero_mul_quot
  mul_zero := mul_quot_zero
  mul_assoc := mul_quot_assoc
  one_mul := one_mul_quot
  mul_one := mul_quot_one
  add_left_neg := add_left_neg_quot }

lemma pos_val_of_quot_zero {x : R} (h : ⟦x⟧.nav = ⟦0⟧) : nav x > 0 := by
  rw [←sub_zero x, ←congruence_p, ←SurjVal.s.r_eq]
  exact Quotient.exact h

lemma quot_pos_val {x : R} (h : nav x > 0) : ⟦x⟧.nav = ⟦0⟧ := by
  rw [Quotient.sound]
  simp [HasEquiv.Equiv, instHasEquiv, SurjVal.s.r_eq, congruence_p, h]

lemma quot_pos_val_mul {x y : R} (h : nav x > 0) : ⟦x * y⟧.nav = ⟦0⟧ := by
  rwa [mul_quot_eq_quot_mul, quot_pos_val, ←mul_quot_eq_quot_mul, zero_mul]

lemma quot_mul_pos_val {x y : R} (h : nav y > 0) : ⟦x * y⟧.nav = ⟦0⟧ := by
  rw [mul_comm, quot_pos_val_mul h]

lemma quot_pow_eq_quot_of_pow {a : R} {n : ℕ} : ⟦a⟧.nav ^ n = ⟦a ^ n⟧ := by
  induction n with
  | zero => simp [pow_zero]; rfl
  | succ n ih =>
    simp [pow_succ, ih, mul_quot_eq_quot_mul]


/- not sure I need those -/
section quot_p
lemma quot_p : ⟦p⟧.nav = ⟦0⟧ := by
  apply quot_pos_val
  simp [nav.v_uniformizer]

lemma quot_p_mul (x : R) : ⟦p * x⟧.nav = ⟦0⟧ := by
  apply quot_pos_val_mul
  simp [nav.v_uniformizer]

lemma quot_mul_p (x : R) : ⟦x * p⟧.nav = ⟦0⟧ := by
  rw [mul_comm, quot_p_mul]
end quot_p


end residue

--set_option pp.all true
structure ResidueRing {p : R} (valtn : SurjVal p) where
  lift' : R → R --lift function
  lift_def : ∀ (a b : R), valtn.s.r a b → lift' a = lift' b
  char : ℕ
  val_char : valtn char > 0
  char_min : ∀ n : ℕ, n.succ < char → valtn.v n.succ = 0

namespace ResidueRing

variable {p : R}
variable {valtn : SurjVal p}

--def repr_p (rr : ResidueRing valtn) (x : R) : Quotient valtn.s := Quotient.mk valtn.s x

--def congr_of_repr : ∀ a b : R, congruence_p valtn a b → repr_p a = repr_p b

lemma quot_char (rr : ResidueRing valtn) : (⟦(rr.char : R)⟧ : Quotient valtn.s) = ⟦0⟧ := by
  rw [Quotient.sound]
  simp [HasEquiv.Equiv, instHasEquiv, SurjVal.s.r_eq, congruence_p, rr.val_char]

lemma quot_char_mul (rr : ResidueRing valtn) (x : R) : (⟦(rr.char : R) * x⟧ : Quotient valtn.s) = ⟦0⟧ := by
  rw [mul_quot_eq_quot_mul, quot_char rr, ←mul_quot_eq_quot_mul, zero_mul]

lemma quot_mul_char (rr : ResidueRing valtn) (x : R) : (⟦x * (rr.char : R)⟧ : Quotient valtn.s) = ⟦0⟧ := by
  rw [mul_comm, quot_char_mul rr]

/- prove might involve that the characteristic is prime (?) -/
-- doesnt look true to alex
-- lemma quot_pow_char (rr : ResidueRing valtn) (x : R) : (⟦x ^ rr.char⟧ : Quotient valtn.s) = ⟦x⟧ := by sorry

end ResidueRing


lemma RingCon.exists_rep (RC : RingCon R) : ∀ a : RC.Quotient, ∃ A : R, A = a :=
Quotient.exists_rep

namespace EnatValRing
variable {R : Type u} [CommRing R] [IsDomain R] {p : R} (evr : EnatValRing p)

def RingCon : RingCon R :=
{ evr.valtn.s with
  add' := add_repr_eq_repr_add evr.valtn _ _ _ _
  mul' := mul_repr_eq_repr_mul evr.valtn _ _ _ _ }

instance : Nontrivial evr.RingCon.Quotient :=
{ exists_pair_ne := by
    refine ⟨(0 : R), (1 : R), ?_⟩
    rw [Ne.def, RingCon.eq, RingCon.rel_mk, SurjVal.s.r_eq, congruence_p]
    simp }

instance : NoZeroDivisors evr.RingCon.Quotient :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    obtain ⟨A, rfl⟩ := evr.RingCon.exists_rep a
    obtain ⟨B, rfl⟩ := evr.RingCon.exists_rep b
    rw [← RingCon.coe_zero] at *
    rw [← RingCon.coe_mul] at *
    rw [RingCon.eq, RingCon.rel_mk, SurjVal.s.r_eq, congruence_p] at *
    rw [RingCon.eq, RingCon.rel_mk, SurjVal.s.r_eq, congruence_p] at *
    aesop }

instance : Field evr.RingCon.Quotient :=
{ inv := fun x => (Quotient.lift evr.inv_mod) sorry x
  mul_inv_cancel := sorry
  inv_zero := sorry }

instance : IsDomain evr.RingCon.Quotient := {}

lemma key : ring_char evr.RingCon.Quotient = evr.residue_char := sorry
instance : PerfectRing evr.RingCon.Quotient :=
{ pth_power_bijective := by
    rw [or_iff_not_imp_left]
    intro h
    rw [Function.Bijective]
    apply And.intro
    . exact pow_ring_char_injective h
    . intro x
      obtain ⟨B, rfl⟩ := evr.RingCon.exists_rep x
      use evr.pth_root B
      rw [key]
      simp only
      rw [← RingCon.coe_pow]
      rw [RingCon.eq, RingCon.rel_mk, SurjVal.s.r_eq, congruence_p]
      apply evr.pth_root_spec }
end EnatValRing
