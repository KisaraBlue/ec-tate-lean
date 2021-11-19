import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Order
import Mathlib.Algebra.Ring.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Nat.NatWithTop

--class ValueMonoid (A : Type u) extends AddCommMonoid A, LinearOrder A

open NatWithTop

structure NormalizedAddValuation {R : Type u} (p : R) [CommRing R] where
  v : R → ℕ∪∞
  v_uniformizer : v p = ofN 1
  v_mul_eq_add_v (a b : R) : v (a * b) = v a + v b
  v_add_ge_min_v (a b : R) : v (a + b) ≥ min (v a) (v b)
  v_eq_top_iff_zero (a : R) : v a = ∞ ↔ a = 0

structure DiscretelyValuedRing {R : Type u} (p : R) extends IntegralDomain R where
  valtn : NormalizedAddValuation p
