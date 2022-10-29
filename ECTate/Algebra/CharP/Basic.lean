import ECTate.Algebra.Field.Basic
import ECTate.Algebra.Ring.Basic
import ECTate.Algebra.EllipticCurve.ValuedRing
import ECTate.Data.Nat.Enat

open Classical
variable (R : Type _) [Semiring R]

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable
def ring_char := if h : _ then Nat.find (fun n => n ≠ 0 ∧ (n : R) = 0) h else 0

lemma ring_char_is_zero_or_prime (R : Type _) [IntegralDomain R] :
  ring_char R = 0 ∨ nat_prime (ring_char R) := sorry
