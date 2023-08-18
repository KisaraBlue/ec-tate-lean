import ECTate.Algebra.EllipticCurve.TateInt

open Int Model ValidModel SurjVal

/-! Following Shankar-Shankar-Wang, Large families of elliptic curves ordered by conductor
-/
variable {p : ℕ} (hp : Nat.Prime p) (hn23 : p ≠ 2 ∧ p ≠ 3) (a b c : ℤ) (habc)

lemma c4_abc : Model.c4 ⟨0, a, 0, b, c⟩ = 16 * a ^ 2 - 48 * b :=
by
  simp [c4, b2, b4]
  ring

lemma discr_abc :
  Model.discr ⟨0, a, 0, b, c⟩ = -16*a^2*(4*a*c - b^2) + 288*a*b*c - 64*b^3 - 432*c^2 :=
by
  simp [discr, b8, b6, b2, b4]
  ring

lemma val_discr_abc :
  val_discr_to_nat (primeEVR hp).valtn ⟨⟨0, a, 0, b, c⟩, habc⟩ =
    nat_of_val (primeEVR hp).valtn (fun h => habc (by rwa [discr_abc]) : (-16*a^2*(4*a*c - b^2) + 288*a*b*c - 64*b^3 - 432*c^2) ≠ 0) :=
by
  rw [ENat.eq_ofN, ofN_val_discr_to_nat]
  conv =>
    lhs
    rw [discr_abc]
  simp [nat_of_val]

-- lemma kodaira_I0 (hcon : (primeEVR hp).valtn (Model.discr ⟨0, a, 0, b, c⟩) = 0) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .I 0 :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   sorry
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 0
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--     sorry
--   simp [valdisc']

-- lemma kodaira_In (n : ℕ) (hn : n ≥ 1)
--   (hcona : (primeEVR hp).valtn a = 0)
--   (hconb : (primeEVR hp).valtn b ≥ ((n + 1)/2 : ℕ))
--   (hconc : (primeEVR hp).valtn c = n) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .I n :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--   simp [valc4, valdisc']

-- lemma kodaira_II
--   (hcona : (primeEVR hp).valtn a ≥ 1)
--   (hconb : (primeEVR hp).valtn b ≥ 1)
--   (hconc : (primeEVR hp).valtn c = 1) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .II :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--   simp [valc4, valdisc']

-- lemma kodaira_III
--   (hcona : (primeEVR hp).valtn a ≥ 1)
--   (hconb : (primeEVR hp).valtn b = 1)
--   (hconc : (primeEVR hp).valtn c ≥ 2) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .III :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--   simp [valc4, valdisc']

-- lemma kodaira_IV
--   (hcona : (primeEVR hp).valtn a ≥ 1)
--   (hconb : (primeEVR hp).valtn b ≥ 2)
--   (hconc : (primeEVR hp).valtn c = 2) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .IV :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--   simp [valc4, valdisc']

-- lemma kodaira_Is0 (hcon : (primeEVR hp).valtn (Model.discr ⟨0, a, 0, b, c⟩) < 7)
--   (hcona : (primeEVR hp).valtn a ≥ 1)
--   (hconb : (primeEVR hp).valtn b ≥ 2)
--   (hconc : (primeEVR hp).valtn c ≥ 3) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .Is 0 :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--   simp [valc4, valdisc']

-- lemma kodaira_Is {n : ℕ} (hn : n ≥ 1)
--   (hcona : (primeEVR hp).valtn a = 1)
--   (hconb : (primeEVR hp).valtn b ≥ ((n + 1)/2 + 2 : ℕ))
--   (hconc : (primeEVR hp).valtn c ≥ n + 3) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .Is n :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--   simp [valc4, valdisc']

-- lemma kodaira_IVs
--   (hcona : (primeEVR hp).valtn a ≥ 2)
--   (hconb : (primeEVR hp).valtn b ≥ 3)
--   (hconc : (primeEVR hp).valtn c = 4) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .IVs :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--   simp [valc4, valdisc']

-- lemma kodaira_IIIs
--   (hcona : (primeEVR hp).valtn a ≥ 2)
--   (hconb : (primeEVR hp).valtn b ≥ 3)
--   (hconc : (primeEVR hp).valtn c ≥ 5) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .IIIs :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--   simp [valc4, valdisc']

-- lemma kodaira_IIs
--   (hcona : (primeEVR hp).valtn a ≥ 2)
--   (hconb : (primeEVR hp).valtn b ≥ 4)
--   (hconc : (primeEVR hp).valtn c = 5) :
--   (tate_algorithm p hp ⟨⟨0, a, 0, b, c⟩, habc⟩).1 = .IIs :=
-- by
--   rw [tate_algorithm, if_neg hn23.1, if_neg hn23.2, tate_big_prime]
--   generalize h : (⟨⟨0,a,0,b,c⟩, _⟩ : ValidModel ℤ) = e
--   have valc4 : 3 * (primeEVR hp).valtn e.c4 = ⊤; simp [← h, c4_abc]
--   have valdisc' : val_discr_to_nat (primeEVR hp).valtn e % 12 = 8
--   . simp [← h, val_discr_abc hp a b c habc, nat_of_val, c4_abc]
--   simp [valc4, valdisc']
