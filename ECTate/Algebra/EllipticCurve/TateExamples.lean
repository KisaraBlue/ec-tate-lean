import ECTate.Algebra.EllipticCurve.TateInt

open Int Model ValidModel


@[simp] lemma b2_mordell (p) : Model.b2 ⟨0,0,0,0, (p : Int)⟩ = 0 := by simp [b2]
@[simp] lemma b4_mordell (p) : Model.b4 ⟨0,0,0,0, (p : Int)⟩ = 0 := by simp [b4]
@[simp] lemma b6_mordell (p) : Model.b6 ⟨0,0,0,0, (p : Int)⟩ = 4 * p := by simp [b6]
@[simp] lemma b8_mordell (p) : Model.b8 ⟨0,0,0,0, (p : Int)⟩ = 0 := by simp [b8]
@[simp] lemma c4_mordell (p) : Model.c4 ⟨0,0,0,0, (p : Int)⟩ = 0 := by simp [c4]
@[simp]
lemma c6_mordell (p) : Model.c6 ⟨0,0,0,0, (p : Int)⟩ = - 864 * p :=
by
  simp only [c6, b2, mul_zero, add_zero, neg_zero, pow_succ, pow_zero, mul_one, b4, b6,
    zero_add, zero_sub, neg_mul, neg_inj]
  rw [← mul_assoc]
  norm_num

@[simp]
lemma discr_mordell (p) : Model.discr ⟨0,0,0,0, (p : Int)⟩ = - 432 * p ^ 2 :=
by
  -- TODO copying simp only message from problems panel causes panic
  -- but now ive changed the proof, go back in time to see problem
  simp only [discr, b2, mul_zero, add_zero, neg_zero, b8, zero_mul, sub_self, b4,
    pow_succ, pow_zero, mul_one,  b6, zero_add, zero_sub, neg_mul, neg_inj]
  ring

-- TODO how does unnecessary simpa work
lemma val_discr_mordell (p : ℕ) (hp : Nat.Prime p) (hn23 : p ≠ 2 ∧ p ≠ 3) (h) :
  val_discr_to_nat (primeEVR hp).valtn ⟨⟨0,0,0,0, b⟩, h⟩ = 2 * (nat_of_val (primeEVR hp).valtn (λ hb => by simp [hb] at h : b ≠ 0)) :=
by
  rw [Enat.eq_ofN, ofN_val_discr_to_nat]
  dsimp
  conv =>
    lhs
    rw [discr_mordell]
  simp [neg_mul, val_neg, SurjVal.v_mul_eq_add_v, nat_of_val] -- need simp lemma coe_of_nat_of_val
  norm_num
  convert zero_add (?_ : Enat) -- TODO lean needs help here why, no _
  sorry
  exact rfl
  exact rfl

lemma Mordell_KodairaTypeII (p) (hp : Nat.Prime p) (hn23 : p ≠ 2 ∧ p ≠ 3) :
  (tate_algorithm p hp ⟨⟨0, 0, 0, 0, p⟩, by simp [hp.ne_zero]⟩).1 = .II := -- TODO maybe expand this to say more about conductor exponent etc
by
  rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
  generalize h : (⟨⟨0,0,0,0,p⟩, _⟩ : ValidModel ℤ) = e
  have valc4 : 3 * (primeEVR hp).valtn e.c4 = ∞ := by
    simp [← h, c4_mordell]
  have valdisc : val_discr_to_nat (primeEVR hp).valtn e = 2 := by
    rw [← h, val_discr_mordell _ _ hn23, nat_of_val]
    simp
  have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 2 := by
    simp [valdisc]
  simp [valc4, valdisc']

lemma Mordell_KodairaTypeIIs (p) (hp : Nat.Prime p) (hn23 : p ≠ 2 ∧ p ≠ 3) :
  (tate_algorithm p hp ⟨⟨0, 0, 0, 0, (p : ℤ)^5⟩, by simp [hp.ne_zero]⟩).1 = .IIs := -- TODO maybe expand this to say more about conductor exponent etc
by
  rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
  generalize h : (⟨⟨0,0,0,0,(p:ℤ)^5⟩, _⟩ : ValidModel ℤ) = e
  have valc4 : 3 * (primeEVR hp).valtn e.c4 = ∞ := by
    simp [← h, c4_mordell]
  have valdisc : val_discr_to_nat (primeEVR hp).valtn e = 10 := by
    rw [← h, val_discr_mordell _ _ hn23, nat_of_val]
    simp [SurjVal.v_uniformizer]
  have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 10 := by
    simp [valdisc]
  simp [valc4, valdisc']

lemma Mordell_KodairaTypeIV (p) (hp : Nat.Prime p) (hn23 : p ≠ 2 ∧ p ≠ 3) :
  (tate_algorithm p hp ⟨⟨0, 0, 0, 0, (p : ℤ)^2⟩, by simp [hp.ne_zero]⟩).1 = .IV := -- TODO maybe expand this to say more about conductor exponent etc
by
  rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
  generalize h : (⟨⟨0,0,0,0,(p : ℤ)^2⟩, _⟩ : ValidModel ℤ) = e
  have valc4 : 3 * (primeEVR hp).valtn e.c4 = ∞ := by
    simp [← h, c4_mordell]
  have valdisc : val_discr_to_nat (primeEVR hp).valtn e = 4 := by
    rw [← h, val_discr_mordell _ _ hn23, nat_of_val]
    simp
  have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 4 := by
    simp [valdisc]
  simp [valc4, valdisc']

lemma Mordell_KodairaTypeIVs (p) (hp : Nat.Prime p) (hn23 : p ≠ 2 ∧ p ≠ 3) :
  (tate_algorithm p hp ⟨⟨0, 0, 0, 0, (p : ℤ)^4⟩, by simp [hp.ne_zero]⟩).1 = .IVs := -- TODO maybe expand this to say more about conductor exponent etc
by
  rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
  generalize h : (⟨⟨0,0,0,0,(p : ℤ)^4⟩, _⟩ : ValidModel ℤ) = e
  have valc4 : 3 * (primeEVR hp).valtn e.c4 = ∞ := by
    simp [← h, c4_mordell]
  have valdisc : val_discr_to_nat (primeEVR hp).valtn e = 8 := by
    rw [← h, val_discr_mordell _ _ hn23, nat_of_val]
    simp
  have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8 := by
    simp [valdisc]
  simp [valc4, valdisc']

-- lemma aa :
--   (tate_big_prime 5 sorry ⟨⟨0, 0, 0, 0, 5⟩, sorry⟩).1 = .II := by
--   dsimp [tate_big_prime]
