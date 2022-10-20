import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring


theorem pow_two {M} [Monoid M] (a : M) : a ^ (2:ℕ) = a * a :=
by rw [pow_succ, pow_one]


variable {R : Type _}

--theorem mul_add (a b c : R) : a * (b + c) = a * b + a * c := Semiring.mul_add a b c

--theorem add_mul (a b c : R) : (a + b) * c = a * c + b * c := Semiring.add_mul a b c

@[simp] lemma one_pow [Semiring R] (n : Nat) : (1 ^ n : R) = 1 := by
  induction n with
  | zero =>
    rw [pow_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    simp

theorem add_self_eq_mul_two [Semiring R] (a : R) : a + a = 2 * a := by
  rw [←one_mul a, ←add_mul, one_mul]
  simp
  sorry

section Ring
--theorem sub_eq_add_neg (a b : R) : a - b = a + -b := Ring.sub_eq_add_neg a b
variable [Ring R]

theorem neg_mul_left (a b : R) : -(a * b) = -a * b := by
  rw [←add_zero (-a * b), ←add_left_neg (a * b)]
  rw [←add_assoc (-a * b), add_comm (-a * b), add_assoc]
  rw [←add_mul, add_left_neg a]
  simp

theorem neg_mul_right (a b : R) : -(a * b) = a * -b := by
  rw [←add_zero (a * -b), ←add_left_neg (a * b)]
  rw [←add_assoc (a * -b), add_comm (a * -b), add_assoc]
  rw [←mul_add, add_left_neg b]
  simp

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, mul_add, ←neg_mul_right, ←sub_eq_add_neg]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, add_mul, ←neg_mul_left, ←sub_eq_add_neg]

@[simp] theorem sub_zero (a : R) : a - 0 = a := by
  rw [sub_eq_add_neg, ←add_zero (-0), add_left_neg (0: R)]
  simp

theorem neg_add (a b : R) : - (a + b) = -a + -b := by
  have h₁ : - (a + b) = -(a + b) + (a + b) + -a + -b := by
    rw [add_assoc, add_comm (-a), add_assoc, add_assoc, ← add_assoc b]
    rw [add_right_neg b, zero_add, add_right_neg a, add_zero]
  rwa [add_left_neg (a + b), zero_add] at h₁

theorem sub_add (a b c : R) : a - (b + c) = a - b - c := by
  rw [sub_eq_add_neg, neg_add, ←add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg]

-- theorem sub_add_comm (n m k : R) : n + m - k = n - k + m := by
--   rw [sub_eq_add_neg, add_assoc, add_comm m, ←add_assoc, ←sub_eq_add_neg]

@[simp] lemma square_neg_one : -1 ^ 2 = (1 : R) := by
  rw [pow_succ, pow_one, ←neg_mul_left, one_mul, neg_neg (1 : R)]

end Ring


section CommRing
variable [CommRing R]


theorem square_neg (a : R) : -a ^ 2 = a ^ 2 := by
  rw [←one_mul a, neg_mul_left, mul_pow _ a, square_neg_one, one_mul, one_mul]

theorem evenpow_neg {n m : ℕ} (a : R) (h : n = 2 * m) : -a ^ n = a ^ n := by
  rw [h, pow_mul, pow_mul, square_neg]

theorem oddpow_neg {n m : ℕ} (a : R) (h : n = 2 * m + 1) : -a ^ n = -(a ^ n) := by
  rw [h, pow_succ, evenpow_neg a (show 2 * m = 2 * m by rfl), ←neg_mul_right, ←pow_succ,
    Nat.add_one]

lemma square_add (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by
  rw [pow_two, mul_add, add_mul, add_mul, ←pow_two, ←pow_two, ←add_assoc, mul_comm b,
    ←one_mul (a * b), add_assoc (a ^ 2), ←add_mul, add_self_eq_mul_two 1, mul_one, one_mul]

lemma square_sub (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * (a * b) + b ^ 2 := by
  rw [sub_eq_add_neg, square_add, square_neg, ←neg_mul_right, ←neg_mul_right, ←sub_eq_add_neg]

end CommRing

class IntegralDomain (R : Type u) extends CommRing R where
  non_trivial : ¬1 = 0
  factors_nzero_mul_nzero {a b : R} : a ≠ 0 → b ≠ 0 → a * b ≠ 0

section IntegralDomain
variable [IntegralDomain R]

theorem non_trivial : ¬1 = 0 := IntegralDomain.non_trivial R

theorem factors_nzero_mul_nzero {a b : R} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := IntegralDomain.factors_nzero_mul_nzero

theorem mul_eq_zero_iff_factor_eq_zero (a b : R) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  apply Iff.intro
  . intro mul_eq_zero
    sorry
  . intro factor_eq_zero
    cases factor_eq_zero with
    | inl a_zero => rw [a_zero, zero_mul]
    | inr b_zero => rw [b_zero, mul_zero]

theorem nzero_mul_left_cancel (a b c : R) : a ≠ 0 → a * b = a * c → b = c := by
  intro a_ne_z ab_eq_ac
  rw [←add_left_inj (-(a * c)), add_neg_self (a * c), neg_mul_right, ←mul_add] at ab_eq_ac
  cases (mul_eq_zero_iff_factor_eq_zero a (b + -c)).1 ab_eq_ac with
  | inl h => exact False.elim (a_ne_z h)
  | inr h =>
    rw [←add_left_inj (-c), add_neg_self c]
    exact h

-- set_option pp.all true
theorem pow_nonzero (a : R) (n : ℕ) : a ≠ 0 → a ^ n ≠ 0 := by
  intro h
  induction n with
  | zero =>
    simp
    intro hh
    apply h
    rw [←one_mul a, hh, zero_mul]
  | succ n ih =>
    rw [pow_succ]
    exact factors_nzero_mul_nzero ih h

end IntegralDomain



--instance : Numeric ℤ := ⟨Int.ofNat⟩

instance : IntegralDomain ℤ where
  __ := inferInstanceAs (CommRing ℤ)
  non_trivial := by sorry
  factors_nzero_mul_nzero := by sorry
