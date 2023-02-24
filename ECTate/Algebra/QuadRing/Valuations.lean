import ECTate.Algebra.QuadRing.Basic
import ECTate.Algebra.ValuedRing

instance : IsDomain $ QuadRing ℤ 0 (-1) := sorry

namespace QuadRing

def gaussian_val (p : ℕ) (k : QuadRing ℤ 0 (-1)) : ℕ∪∞ :=
  min (Int.int_val p k.b1) (Int.int_val p k.b2)

@[simp]
lemma gaussian_val_uniformizer {p : ℕ} (gt1 : 1 < p) : gaussian_val p p = 1 := by
  rw [gaussian_val]
  simp [gt1]

lemma gaussian_val_mul_eq_add {p : ℕ} (prime : Nat.Prime p) (a b : QuadRing ℤ 0 (-1)) :
  gaussian_val p (a * b) = gaussian_val p a + gaussian_val p b := by
  simp [gaussian_val]
  sorry

lemma gaussian_val_add_ge_min (p : ℕ) (a b : QuadRing ℤ 0 (-1)) :
  gaussian_val p (a + b) ≥ min (gaussian_val p a) (gaussian_val p b) := by
  simp [gaussian_val]
  sorry

lemma eq_top_of_min_eq_top (a b : ℕ∪∞) : min a b = ∞ → a = ∞ :=
by
  sorry

@[simp]
lemma min_eq_top_iff (a b : ℕ∪∞) : min a b = ∞ ↔ a = ∞ ∧ b = ∞ :=
by
  -- aesop
  sorry

lemma gaussian_val_eq_top_iff_zero {p : ℕ} (gt1 : 1 < p) (a : QuadRing ℤ 0 (-1)) :
  gaussian_val p a = ∞ ↔ a = 0 :=
by simp [gaussian_val, gt1, QuadRing.ext_iff]

def primeVal {p : ℕ} (hp : Nat.Prime p) (hpi : p % 4 = 1) : SurjVal (p : QuadRing ℤ 0 (-1)) := {
  v := gaussian_val p
  v_uniformizer' := gaussian_val_uniformizer hp.one_lt
  v_mul_eq_add_v' := gaussian_val_mul_eq_add hp
  v_add_ge_min_v' := gaussian_val_add_ge_min p
  v_eq_top_iff_zero' := gaussian_val_eq_top_iff_zero hp.one_lt }


def decr_val_p (p : ℕ) (k : QuadRing ℤ 0 (-1)) : QuadRing ℤ 0 (-1) :=
  if k.b1 % p == 0 ∧ k.b2 % p == 0 then ⟨k.b1 / p, k.b2 / p⟩ else k

def norm_repr_p (p : ℕ) (x : QuadRing ℤ 0 (-1)) : QuadRing ℤ 0 (-1) :=
⟨Int.norm_repr_p p x.b1,
 Int.norm_repr_p p x.b2⟩

def primeEVR {p : ℕ} (hp : Nat.Prime p) (hpi  : p % 4 = 1) : EnatValRing (p : QuadRing ℤ 0 (-1)) :=
{ valtn := primeVal hp hpi
  decr_val := decr_val_p p
  zero_valtn_decr := sorry
  pos_valtn_decr := sorry
  residue_char := p
  norm_repr := norm_repr_p p
  norm_repr_spec := sorry
  quad_roots_in_residue_field := sorry
  inv_mod := sorry
  inv_mod_spec := sorry
  inv_mod_spec' := sorry
  inv_mod_spec'' := sorry
  pth_root := (. ^ p)
  pth_root_spec := sorry
  count_roots_cubic := sorry }


#eval (primeEVR (by norm_num : Nat.Prime 5) (by norm_num)).valtn ⟨1,5⟩
#eval (primeEVR (by norm_num : Nat.Prime 5) (by norm_num)).valtn ⟨-50,5⟩

end QuadRing
