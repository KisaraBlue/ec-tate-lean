import ECTate.Tactic.ELinarith
import Mathlib.Algebra.Ring.Pi



lemma v_b6_of_v_a3_a {q : ℕ} (h : (q : Enat) ≥ 2): q ≥ (1 : Enat) := by
  elinarith


def tt : Enat -> Enat := sorry
example (x : Enat) (h : 1 ≤ tt x) : 2 ≤ 1 + tt x :=
by
  elinarith

example (x : Enat) (h : 0 < x) : 2 ≤ 1 + x :=
by
  elinarith

example (x : Enat) (h : 0 < x) : 3 ≤ 1 + 2 * x :=
by
  elinarith

example (x : Enat) (h : 0 < x) : (x + 1) ≤ x + 2 + x :=
by
  elinarith

example (x : Enat) (h : 0 < x) : 3 ≤ 1 + 2 * x :=
by
  cases x
  simp at *
  norm_cast at *
  linarith
  simp


example (y  x : Enat) (h : 0 < y) (g : y ≤ 3) : y < 2 * y :=
by
  elinarith
example (x y : Enat) (h : 0 < x) (g : 3 ≤ y) : 3 ≤ 1 + 2 * x + y :=
by
  elinarith

example (y : Nat) (h : 0 < (y : Enat)) (g : (y : Enat) ≤ 3) : (y : Enat) < 2 * y :=
by
  elinarith



#check NonAssocRing.toNatCast
#check Semiring.toNatCast
def a3 (R) : R := sorry
def a6 (R) : R := sorry
def b6 (R) [CommRing R] : R := sorry
def SurjVal' R (p : R) : Type := sorry
def v {p : R} : SurjVal' R p → R → Enat := sorry
-- R: Type u
-- inst✝: CommRing R
-- inst: IsDomain R
-- p: R
-- q: ℕ
-- valp: SurjVal p
-- e: ValidModel R
-- h3: v valp e.toModel.a3 ≥ ↑q
-- h6: v valp e.toModel.a6 ≥ 2 * ↑q
-- ⊢ 2 * ↑q ≤ v valp (e.toModel.a3 * e.toModel.a3 + 4 * e.toModel.a6)

-- lemma v_b6_of_v_a3_a6  --{p : R}
-- {q : ℕ} --(valp : SurjVal p) (e : ValidModel R)-- (h3 : valp e.a3 ≥ q)
--   -- (h6 : valp e.a6 ≥ 2 * q)
--   : q ≥ (1 : Enat) := by
--   elinarith

-- -- set_option pp.raw  true in
-- example [CommRing R] (p : R) {q : ℕ} (valp : SurjVal' R p)
--  : v valp (a3 R * a3 R + 4 * a6 R) ≥ 2 * q := by
--   simp
--   elinarith
  -- sorry
