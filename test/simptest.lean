import ECTate.Tactic.SimpSafe
import Mathlib.Tactic


open ECTate.Tactic
def t : Nat := sorry
def s : Nat := sorry
def w : Nat := sorry
lemma teqs : t = s := sorry

example (hoof : t = s) : t = w * s := by
  -- simp_safe only [hoof] at hoof
  -- simp_safe only [← hoof] at hoof
  set_option trace.Meta.Tactic.simp.rewrite true in
  simp_safe_all [← hoof]


 #exit

example (hoof : t = s) : t = w * s := by
  -- simp_safe only [hoof] at hoof
  -- simp_safe only [← hoof] at hoof
  simp_safe [hoof] at *

structure X where
(wp x y zp ap bp : Nat)
structure X where
(wp x y zp ap bp : Nat)

set_option pp.raw true
open Nat
example (u : X) : u = u := by
  let ⟨wp, x, y, zp, ap, bp⟩ := u

  have h : wp + zp + wp * zp = x * y := sorry
  have : (wp + 1) * (zp + 1) = (x * y) + 1
  simp_safe_all [← h]
