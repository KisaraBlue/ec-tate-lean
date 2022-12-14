import ECTate.Algebra.Field.Basic
import ECTate.Algebra.Ring.Basic
import ECTate.Algebra.ValuedRing
import ECTate.Data.Nat.Enat
import Mathlib.Tactic.GeneralizeProofs
import Mathlib.Init.Data.Nat.Lemmas

open Classical
variable (R : Type _) [Semiring R]

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable
def ring_char := if h : _ then @Nat.find (fun n => n ≠ 0 ∧ (n : R) = 0) _ h else 0

lemma ring_char_eq_zero (R : Type _) [Semiring R] :
  (ring_char R : R) = 0 :=
by
  rw [ring_char]
  split
  . exact (And.right (Nat.find_spec (by assumption)))
  . simp


lemma ring_char_dvd_of_zero {R : Type _} [Ring R] (h : (m : R) = 0) :
  ring_char R ∣ m :=
by
  by_cases hm : m = 0
  . simp [hm, Nat.dvd_zero] at *
  . rw [ring_char]
    rw [dif_pos ?_]

    rotate_right 1 -- swap -- TODO unknown swap
    exists m
    generalize_proofs hh
    have := Nat.find_spec hh
    rw [Nat.gcd_eq_left_iff_dvd]
    sorry

lemma ring_char_is_zero_or_prime (R : Type _) [IntegralDomain R] :
  ring_char R = 0 ∨ nat_prime (ring_char R) := sorry
