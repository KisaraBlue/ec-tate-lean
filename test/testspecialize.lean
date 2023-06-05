import ECTate.Tactic.Specialize
import Mathlib.Tactic.PrintPrefix
universe u
-- #check (fun (a : Type u) => 1) ℕ

@[specialize ℕ]
def g (R : Type _) [Ring R] (n : ℕ) : R := List.sum $ List.replicate n (1 : R)

#check g_spec
set_option profiler true
#eval g ℤ 20000000
#eval g_spec 20000000
-- def f (n : ℕ) := List.sum $ List.replicate n (1 : ℤ)
def h (R : Type _) [Ring R] (l : List R) : R := match l with
| [] => 0
| a :: l => a + h R l

set_option trace.compiler true
@[specialize ℤ]
def f := h

#eval f ℤ (List.replicate 2000 1)
#eval f_spec (List.replicate 2000 1)


#print g_spec
#print prefix g
#print g
#print h
