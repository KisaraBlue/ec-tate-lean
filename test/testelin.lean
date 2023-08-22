import ECTate.Tactic.ELinarith
import Mathlib.Algebra.Ring.Pi



lemma v_b6_of_v_a3_a {q : ℕ} (h : (q : ENat) ≥ 2) : q ≥ (1 : ENat) := by
  elinarith

-- set_option trace.profiler true
-- set_option profiler true
def tt : ENat -> ENat := sorry
example (x : ENat) (h : 1 ≤ tt x) : 2 ≤ 1 + tt x :=
by
  elinarith

example (x : ENat) (h : 0 < x) : 2 ≤ 1 + x :=
by
  elinarith

example (x : ENat) (h : 0 < x) : 3 ≤ 1 + 2 * x :=
by
  elinarith

example (x : ENat) (h : 0 < x) : (x + 1) ≤ x + 2 + x :=
by
  elinarith

example (x : ENat) (h : 0 < x) : 3 ≤ 1 + 2 * x :=
by
  cases x
  simp at *
  norm_cast at *
  linarith


example (y  x : ENat) (h : 0 < y) (g : y ≤ 3) : y < 2 * y :=
by
  elinarith
example (x y : ENat) (h : 0 < x) (g : 3 ≤ y) : 3 ≤ 1 + 2 * x + y :=
by
  elinarith

example (y : Nat) (h : 0 < (y : ENat)) (g : (y : ENat) ≤ 3) : (y : ENat) < 2 * y :=
by
  elinarith


-- TODO should also be able to prove this
example (x y z : ENat) (g : x < y) (h : y < z) : x < z :=
by
  elinarith


#check NonAssocRing.toNatCast
#check Semiring.toNatCast
def a3 (R) : R := sorry
def a6 (R) : R := sorry
def b6 (R) [CommRing R] : R := sorry
def SurjVal' R (p : R) : Type := sorry
def v {p : R} : SurjVal' R p → R → ENat := sorry
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
--   : q ≥ (1 : ENat) := by
--   elinarith

-- -- set_option pp.raw  true in
-- example [CommRing R] (p : R) {q : ℕ} (valp : SurjVal' R p)
--  : v valp (a3 R * a3 R + 4 * a6 R) ≥ 2 * q := by
--   simp
--   elinarith
  -- sorry
