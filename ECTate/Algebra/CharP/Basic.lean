import ECTate.Algebra.Field.Basic

open Classical
variable (R : Type _) [Semiring R]

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable
def ring_char := if h : _ then Nat.find (fun n => n ≠ 0 ∧ (n : R) = 0) h else 0
