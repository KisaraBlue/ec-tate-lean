import ECTate.Algebra.Field.Basic
import ECTate.Algebra.Ring.Basic
import ECTate.Algebra.ValuedRing
import ECTate.Data.Nat.Enat
import Mathlib.Tactic.GeneralizeProofs
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Algebra.CharP.Basic

open Classical
variable (R : Type _) [Semiring R]


lemma ringChar_is_zero_or_prime (R : Type _) [NonAssocSemiring R] [NoZeroDivisors R] [Nontrivial R]:
  ringChar R = 0 ∨ Nat.Prime (ringChar R) :=
(CharP.char_is_prime_or_zero R (ringChar R)).symm

lemma add_pow_ringChar {R : Type _} [CommRing R] [IsDomain R] (h : ringChar R ≠ 0) :
  (a + b) ^ ringChar R =
  a ^ ringChar R +
  b ^ ringChar R := by sorry


lemma sub_pow_ringChar {R : Type _} (a b : R) [CommRing R] [IsDomain R] (h : ringChar R ≠ 0) :
  (a - b) ^ ringChar R =
  a ^ ringChar R -
  b ^ ringChar R := by sorry


lemma pow_ringChar_injective {R : Type _} [CommRing R] [IsDomain R]
  (hn : ringChar R ≠ 0) : Function.Injective (. ^ ringChar R : R → R) := by
  intros x y h
  rw [←sub_eq_zero] at *
  rw [←sub_eq_zero] at *
  simp only [sub_zero] at *
  rw [← sub_pow_ringChar _ _ hn] at h
  exact pow_eq_zero h
