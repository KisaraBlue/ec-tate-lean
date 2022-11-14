import ECTate.Algebra.EllipticCurve.TateInt

open Int Model ValidModel

lemma c4_mordell (p) : Model.c4 ⟨0,0,0,0, (p : Int)⟩ = 0 :=
by simp [c4, b2, b4]

lemma c6_mordell (p) : Model.c6 ⟨0,0,0,0, (p : Int)⟩ = - 864 * p :=
by
  simp only [c6, b2, mul_zero, add_zero, neg_zero, pow_succ, pow_zero, mul_one, b4, b6,
    zero_add, zero_sub, neg_mul, neg_inj]
  rw [← mul_assoc]
  norm_num

lemma discr_mordell (p) : Model.discr ⟨0,0,0,0, (p : Int)⟩ = - 432 * p ^ 2 :=
by
  -- TODO copying simp only message from problems panel causes panic
  simp only [discr, b2, mul_zero, add_zero, neg_zero, b8, zero_mul, sub_self, b4,
    pow_succ, pow_zero, mul_one,  b6, zero_add, zero_sub, neg_mul, neg_inj]
  ring

lemma val_discr_mordell (p : ℕ) (hp : nat_prime p) (hn23 : p ≠ 2 ∧ p ≠ 3) (h) :
  val_discr_to_nat (primeEVR hp).valtn ⟨⟨0,0,0,0, (p : Int)⟩, h⟩ = 2 :=
by
  rw [Enat.eq_ofN, ofN_val_discr_to_nat, discr_mordell]
  simp only [neg_mul, val_neg]
  rw [pow_two, SurjVal.v_mul_eq_add_v, SurjVal.v_mul_eq_add_v] -- TODO simp lemmas v_pow, v_uniformizer_pow
  rw [SurjVal.v_uniformizer]
  norm_num
  convert zero_add (2 : Enat) -- TODO lean needs help here why, no _
  sorry

lemma Mordell_KodairaTypeII (p) (hp : nat_prime p) (hn23 : p ≠ 2 ∧ p ≠ 3) :
  (tate_big_prime p hp ⟨⟨0, 0, 0, 0, p⟩, sorry⟩).1 = .II := -- TODO maybe expand this to say more about conductor exponent etc
by
  rw [tate_big_prime]
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

-- lemma aa :
--   (tate_big_prime 5 sorry ⟨⟨0, 0, 0, 0, 5⟩, sorry⟩).1 = .II := by
--   dsimp [tate_big_prime]
