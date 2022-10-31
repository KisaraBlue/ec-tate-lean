import ECTate.Algebra.Field.Basic
import ECTate.Algebra.Ring.Basic
import ECTate.Algebra.ValuedRing
import ECTate.Data.Nat.Enat

open Classical
variable (R : Type _) [Semiring R]

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable
def ring_char := if h : _ then Nat.find (fun n => n ≠ 0 ∧ (n : R) = 0) h else 0

lemma ring_char_eq_zero (R : Type _) [IntegralDomain R] :
  (ring_char R : R) = 0 :=
by
  rw [ring_char]
  split
  . exact (Nat.find_spec (fun n => n ≠ 0 ∧ (n : R) = 0) (by assumption)).2
  . simp


lemma ring_char_is_zero_or_prime (R : Type _) [IntegralDomain R] :
  ring_char R = 0 ∨ nat_prime (ring_char R) := sorry
