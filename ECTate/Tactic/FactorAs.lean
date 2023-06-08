import Mathlib.Tactic.Ring


/--
write_as (a - 1) * (b - 1)
ring_change (a - 1) * (b - 1)
group_change a * b = ac_change
group_change a * b = assoc_change
change ring_nf
change ring_nf at

on the goal -a - b + a * b + 1
-/

example [CommRing R] (r : R) : r + r^2 + 1 = 0 :=
by
  convert_to (r + 1) ^ 2 = 0
  admit
  admit
