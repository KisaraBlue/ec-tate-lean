import Mathlib.Algebra.Ring.Basic
import ECTate.Algebra.Ring.Basic
import Mathlib.Logic.Nontrivial


class DivisionRing (K : Type u) extends Ring K, DivInvMonoid K, Nontrivial K :=
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)

class Field (K : Type u) extends CommRing K, DivisionRing K

instance (K : Type u) [h : Field K] : IntegralDomain K :=
{ h with
  non_trivial := by
    obtain ⟨x : K, y, h⟩ := Nontrivial.exists_pair_ne
    intro hh
    apply h
    rw [← one_mul x, hh, zero_mul,
        ← one_mul y, hh, zero_mul]
  factors_nzero_mul_nzero := by
    intro a b ha hb
    sorry}
