--import Mathlib.Init.Data.Int.Basic
--import Mathlib.Init.Algebra.Functions
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic.LibrarySearch

lemma mod_neg_right (m k : Int) : m % (-k) = m % k := by simp
lemma div_neg_left (m k : Int) : (-m) / k = -(m / k) := by simp
lemma div_neg_right (m k : Int) : m / (-k) = -(m / k) := by simp


namespace Int

@[simp] lemma ofNat_zero_eq_zero : ofNat Nat.zero = 0 :=
rfl

end Int
