import ECTate.Algebra.EllipticCurve.TateInt
import ECTate.Algebra.ValuedRing

open Int Model ValidModel


variable (e : ValidModel ℤ) (hp: nat_prime p) (n : ℤ)
#check tate_small_prime 2 (Int.prime_2) e
#check (e.c4 ^ 3)
#check (SurjVal.v (primeEVR hp).valtn (e.c4 ^ 3))
#check (SurjVal.v (primeEVR hp).valtn n)

example : (SurjVal.v (primeEVR hp).valtn (n^2)) = 2 * (SurjVal.v (primeEVR hp).valtn n)
                                                 :=
by simp [val_pow_eq_of_eq]

--lemma val_pow_eq_of_eq {p : R} (nav : SurjVal p) {a : R} (k : ℕ) (ha : nav.v a = m) :
--nav.v (a ^ k) = k * m :=

example : (SurjVal.v (primeEVR hp).valtn (n * n))=(SurjVal.v (primeEVR hp).valtn n) + (SurjVal.v (primeEVR hp).valtn n)
                                                 :=
by library_search

example : (SurjVal.v (primeEVR hp).valtn (n^3))=3 * (SurjVal.v (primeEVR hp).valtn n)
                                                 :=
by library_search

#check SurjVal.v_mul_eq_add_v (primeEVR hp).valtn n n
#check SurjVal.v

#check val_pow_eq_of_eq

#check SurjVal.v_mul_eq_add_v
lemma Mordell_KodairaTypeI_big  (hp : nat_prime p) (hn23 : p ≠ 2 ∧ p ≠ 3) (e : ValidModel ℤ)
(hc4 : SurjVal.v (primeEVR hp).valtn (e.c4) = 0) :
  (tate_big_prime p hp e).1 = .I (val_discr_to_nat ((primeEVR hp).valtn) e) :=
by
rw [tate_big_prime]
have valc4 : SurjVal.v (primeEVR hp).valtn (e.c4 ^ 3) = 0 := by
    simp [hc4, pow_succ]
sorry
 /- rw [tate_big_prime]
  generalize h : (⟨⟨0,0,0,0,p⟩, _⟩ : ValidModel ℤ) = e
  have valc4 : SurjVal.v (primeEVR hp).valtn (e.c4 ^ 3) = ∞ := by
    simp [← h, c4_mordell, pow_succ]
  have valdisc : val_discr_to_nat (primeEVR hp).valtn e = 2 := by
    rw [← h, val_discr_mordell _ _ hn23]
  have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 2 := by
    simp [valdisc]
  simp only [valc4, valdisc, valdisc']
  rw [if_neg]
  exact not_false

  (primeEVR hp).valtn

  let evrp := primeEVR hp
  let navp := evrp.valtn
  let c4 := e.c4
  let c6 := e.c6
  let Δ := e.discr
  let n := val_discr_to_nat navp e

  val_discr_to_nat ((primeEVR hp).valtn) e
  -/

  #check Mordell_KodairaTypeI_big

lemma Mordell_KodairaTypeI (hp : nat_prime p) (e : ValidModel ℤ)
(hc4 : SurjVal.v (primeEVR hp).valtn (e.c4) = 0) :
  (tate_algorithm p hp e).1 = .I (val_discr_to_nat ((primeEVR hp).valtn) e) :=
  if h2 : p = 2 then
    sorry
    --tate_small_prime 2 (Int.prime_2) e
  else if h3 : p = 3 then
    sorry
    --tate_small_prime 3 (Int.prime_3) e
  else by
    rw [tate_algorithm]
    simp[h2,h3]
    exact Mordell_KodairaTypeI_big hp ⟨h2,h3⟩ e hc4

theorem boom' : -2147483648 + 2147483648 = -18446744069414584320 := by
native_decide

#eval -2147483648 + 2147483648
#reduce -2147483648 + 2147483648

#eval -3147483648 + 3147483648

#eval -(2^30)+2^30
#eval -(2^31)+2^31
#eval -(2^32)+2^32

#eval -(2^16)+2^16
#eval -(2^31)+2^31
#eval -(2^32)+2^32
