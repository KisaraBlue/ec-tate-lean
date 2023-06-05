import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.LibrarySearch


/-- A perfect ring is one where raising to the power of the ring characteristic is a bijection
-/
class PerfectRing (R : Type _) [CommSemiring R] :=
(pth_power_bijective : ringChar R = 0 ∨ Function.Bijective (fun x : R => x ^ (ringChar R)))

namespace PerfectRing
variable {R : Type _} [CommSemiring R]

lemma pth_power_bijective_of_char_nonzero [PerfectRing R] (h : ringChar R ≠ 0) :
  Function.Bijective (fun x : R => x ^ (ringChar R)) :=
Or.resolve_left pth_power_bijective h

noncomputable
def pth_root [PerfectRing R] : R → R :=
if h : ringChar R = 0 then id else Function.surjInv (pth_power_bijective_of_char_nonzero h).2

lemma pth_root_pow_char [PerfectRing R] (h : ringChar R ≠ 0) (x : R) :
  pth_root x ^ (ringChar R) = x :=
by
  simp only [pth_root, h, dite_false]
  exact Function.rightInverse_surjInv (pth_power_bijective_of_char_nonzero h).2 x

lemma pth_root_pow_eq [PerfectRing R] (x : R) :
  pth_root x ^ n = x ^ (n / ringChar R) * pth_root x ^ (n % ringChar R) :=
by
  by_cases h : ringChar R = 0
  . simp [h]
  conv =>
    lhs
    rw [← Nat.mod_add_div n (ringChar R)]
  rw [pow_add, pow_mul, pth_root_pow_char h, mul_comm]


@[simp]
lemma pth_root_zero [PerfectRing R] : pth_root (0 : R) = 0 :=
by
  rw [pth_root]
  split
  . simp
  . apply_fun (fun x : R => x ^ ringChar R)
    . simp only [ne_eq]
      rw [Function.surjInv_eq
            (pth_power_bijective_of_char_nonzero (by assumption)).surjective,
          zero_pow]
      rwa [zero_lt_iff]
    . exact (pth_power_bijective_of_char_nonzero (by assumption)).injective

end PerfectRing
