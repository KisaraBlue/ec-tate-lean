import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic


#check List.replicate
open List
-- set_option trace.compiler true
-- set_option trace.Compiler true
def f (n : ℕ) := List.sum $ List.replicate n (1 : ℤ)

def g (R : Type _) [Ring R] (n : ℕ) : R := List.sum $ List.replicate n (1 : R)

set_option profiler true
#eval g ℤ 1000000
#eval f   1000000

-- #eval List.sum._at.f._spec_1 [1,2]
-- #eval fg  100000
variable (a : Nat)

#reduce 1 + (a + 1)
