import Mathlib.Algebra.Ring.Basic
import ECTate.Algebra.Ring.Basic



-- TODO for now the empty division ring is allowed
class DivisionRing (K : Type u) extends Ring K, DivInvMonoid K :=
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)

class Field (K : Type u) extends CommRing K, DivisionRing K

instance (K : Type u) [Field K] : IntegralDomain K := sorry
