--import Mathlib.Init.Data.Int.Basic
--import Mathlib.Init.Algebra.Functions
import Mathlib.Init.Data.Nat.Lemmas

lemma mod_neg_left (m k : Int) : (-m) % k = -(m % k) := by sorry
lemma mod_neg_right (m k : Int) : m % (-k) = m % k := by sorry
lemma div_neg_left (m k : Int) : (-m) / k = -(m / k) := by sorry
lemma div_neg_right (m k : Int) : m / (-k) = -(m / k) := by sorry


namespace Int

@[simp] lemma ofNat_zero_eq_zero : ofNat Nat.zero = 0 :=
rfl

lemma mod_add_div (m k : Int) : m % k + k * (m / k) = m := by
  sorry

end Int
