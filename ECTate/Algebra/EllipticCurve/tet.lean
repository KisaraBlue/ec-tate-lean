import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic


#check List.replicate
open List
set_option trace.compiler.ir true
set_option trace.compiler.code_gen true
def f (n : ℕ) := List.sum $ List.replicate n (1 : ℤ)

def g (R : Type _) [Ring R] (n : ℕ) : R := List.sum $ List.replicate n (1 : R)

set_option profiler true
#eval g ℤ 100000000
#eval f   100000000
