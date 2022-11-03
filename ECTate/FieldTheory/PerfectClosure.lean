import Mathlib.Algebra.Ring.Basic
import ECTate.Algebra.CharP.Basic


/-- A perfect ring is one where raising to the power of the ring characteristic is a bijection
-/
class PerfectRing (R : Type _) [CommSemiring R] :=
(pth_power_bijective : ring_char R = 0 ∨ Function.Bijective (fun x : R => x ^ (ring_char R)))

namespace PerfectRing
variable {R : Type _} [CommSemiring R]

lemma pth_power_bijective_of_char_nonzero [PerfectRing R] (h : ring_char R ≠ 0) :
  Function.Bijective (fun x : R => x ^ (ring_char R)) :=
Or.resolve_left pth_power_bijective h

noncomputable
def pth_root [PerfectRing R] : R → R :=
if h : ring_char R = 0 then id else Function.surjInv (pth_power_bijective_of_char_nonzero h).2

lemma pth_root_pow_char [PerfectRing R] (h : ring_char R ≠ 0) (x : R) :
  pth_root x ^ (ring_char R) = x :=
by
  simp only [pth_root, h, dite_false]
  exact Function.right_inverse_surj_inv (pth_power_bijective_of_char_nonzero h).2 x

@[simp]
lemma pth_root_zero [PerfectRing R] : pth_root (0 : R) = 0 :=
by
  rw [pth_root]
  split
  . simp
  . sorry

end PerfectRing
