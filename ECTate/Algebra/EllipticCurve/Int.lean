/-
multiplicative urst tIso
all quantities x_i => u ^ i | x_i
u tIso => x'_i = u ^ i * x_i
separate u tIso and rst tIso

termination of kronecker symbol

mathport src/data/int from mathlib

-/


import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Init.Data.Int.Basic

-- My lemmas


lemma exact_div {a b : ℤ} : b ∣ a → b * (a / b) = a := by sorry
lemma div_exact {a b : ℤ} : b * (a / b) = a → b ∣ a := by sorry
lemma exact_div_mul {a b c d : ℤ} : b ∣ a → d ∣ c →
  a / b * (c / d) = a * c / (b * d) := by sorry
lemma add_div {a b c : ℤ} : c ∣ a → c ∣ b →
  (a + b) / c = a / c + b / c := by sorry
lemma mul_div_assoc (a : ℤ) {b c : ℤ} : c ∣ b →
  a * b / c = a * (b / c) := by sorry
lemma mul_mod_eq_zero (a : ℤ) {b c : ℤ} : c ∣ b →
  c ∣ (a * b) := by sorry
lemma mul_mod {a b c d : ℤ} : b ∣ a → d ∣ c →
  (b * d) ∣ (a * c) := by sorry

-- Tate's algoritm

structure Model where
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a4 : ℤ
  a6 : ℤ

namespace Model

def b_2 (e : Model) : ℤ := e.a1 * e.a1 + 4 * e.a2

def b_4 (e : Model) : ℤ := e.a1 * e.a3 + 2 * e.a4

def b_6 (e : Model) : ℤ := e.a3 * e.a3 + 4 * e.a6

def b_8 (e : Model) : ℤ :=
  e.a1*e.a1*e.a6 - e.a1*e.a3*e.a4 + 4*e.a2*e.a6 + e.a2*e.a3*e.a3 - e.a4*e.a4

def discr (e : Model) : ℤ :=
  let (b2, b4, b6, b8) := (e.b_2, e.b_4, e.b_6, e.b_8);
  -b2*b2*b8 - 8*(b4 ^ 3) - 27*b6*b6 + 9*b2*b4*b6

lemma b2_div (e : Model) (p : ℤ) :
p ∣ e.a1 → p ^ 2 ∣  e.a2 → p ^ 2 ∣  e.b_2 :=
by
  intro h1 h2
  apply div_exact
  show p ^ 2 * (b_2 e / p ^ 2) = e.a1 * e.a1 + 4 * e.a2
  rw [←exact_div h1]
  rw [mul_assoc p (e.a1 / p), ← mul_assoc (e.a1 / p), mul_comm (e.a1 / p), mul_assoc p (e.a1 / p), ← mul_assoc]
  rw [exact_div_mul h1 h1]
  rw [←exact_div h2]
  rw [← mul_assoc 4, mul_comm 4, mul_assoc _ 4]
  conv in p * p => rw [← pow_one p, ← pow_add]
  rw [← mul_add (p ^ 2)]
  rw [← mul_div_assoc 4 h2]
  rw [← add_div _ (mul_mod_eq_zero 4 h2)]
  show p ^ 2 * (b_2 e / p ^ 2) = p ^ 2 * (b_2 e / p ^ 2)
  simp
  rw [pow_succ, pow_one, mul_mod _ _ _ _ h1 h1]

lemma b4_div (e : Model) (p : ℤ) :
p ∣ e.a1 → p ^ 3 ∣  e.a3 → p ^ 4 ∣  e.a4 → p ^ 4 ∣  e.b_4 :=
by
  intro h1 h3 h4
  apply div_exact
  show p ^ 4 * (b_4 e / p ^ 4) = e.a1 * e.a3 + 2 * e.a4
  rw [←exact_div e.a1 p h1, ←exact_div _ _ h3]
  rw [mul_assoc p (e.a1 / p), ← mul_assoc (e.a1 / p), mul_comm (e.a1 / p), mul_assoc (p^3) (e.a1 / p), ← mul_assoc]
  rw [exact_div_mul _ _ _ _ h1 h3]
  rw [←exact_div _ _ h4]
  rw [← mul_assoc 2, mul_comm 2, mul_assoc _ 2]
  conv in p * p^3 => rw [← pow_one p, ← pow_mul, ← pow_add]
  rw [← mul_add (p ^ 4)]
  rw [← mul_div_assoc _ _ _ h4]
  rw [← add_div _ _ _ _ (mul_mod_eq_zero _ _ _ h4)]
  show p ^ 4 * (b_4 e / p ^ 4) = p ^ 4 * (b_4 e / p ^ 4)
  simp
  rw [pow_succ, mul_comm, mul_mod _ _ _ _ h3 h1]

lemma b6_div (e : Model) (p : ℤ) :
p ^ 3 ∣ e.a3 → p ^ 6 ∣  e.a6 → p ^ 6 ∣  e.b_6 :=
by
  intro h3 h6
  apply div_exact
  show p ^ 6 * (b_6 e / p ^ 6) = e.a3 * e.a3 + 4 * e.a6
  rw [←exact_div h3]
  rw [mul_assoc (p^3) (e.a3 / p^3), ← mul_assoc (e.a3 / p^3), mul_comm (e.a3 / p^3), mul_assoc (p^3) (e.a3 / p^3), ← mul_assoc]
  rw [exact_div_mul h3 h3]
  rw [←exact_div e.a6 _ h6]
  rw [← mul_assoc 4, mul_comm 4, mul_assoc _ 4]
  conv in p^3 * p^3 => rw [← pow_add]
  rw [← mul_add (p ^ 6)]
  rw [← mul_div_assoc _ _ _ h6]
  rw [← add_div _ _ _ _ (mul_mod_eq_zero _ _ _ h6)]
  show p ^ 6 * (b_6 e / p ^ 6) = p ^ 6 * (b_6 e / p ^ 6)
  simp
  rw [pow_add _ 3 3, mul_mod _ _ _ _ h3 h3]

lemma b8_div (e : Model) (p : ℤ) :
p ∣ e.a1 → p ^ 2 ∣ e.a2 → p ^ 3 ∣ e.a3 → p ^ 4 ∣ e.a4 → p ^ 6 ∣  e.a6 → p ^ 8 ∣ e.b_8 :=
by
  intro h1 h2 h3 h4 h6
  apply div_exact
  show p ^ 8 * (b_8 e / p ^ 8) = b_8 e
  rw [←exact_div e.a1 p h1, ←exact_div _ _ h3]
  rw [mul_assoc p (e.a1 / p), ← mul_assoc (e.a1 / p), mul_comm (e.a1 / p), mul_assoc (p^3) (e.a1 / p), ← mul_assoc]
  rw [exact_div_mul _ _ _ _ h1 h3]
  rw [←exact_div _ _ h4]
  rw [← mul_assoc 2, mul_comm 2, mul_assoc _ 2]
  conv in p * p^3 => rw [← pow_one p, ← pow_mul, ← pow_add]
  rw [← mul_add (p ^ 4)]
  rw [← mul_div_assoc _ _ _ h4]
  rw [← add_div _ _ _ _ (mul_mod_eq_zero _ _ _ h4)]
  show p ^ 4 * (b_4 e / p ^ 4) = p ^ 4 * (b_4 e / p ^ 4)
  simp
  rw [pow_succ, mul_comm, mul_mod _ _ _ _ h3 h1]

end Model

structure ValidModel extends Model where
  discr_non_zero : toModel.discr ≠ 0

namespace ValidModel

def discr (e : ValidModel) : ℤ := e.toModel.discr

def c_4 (e : ValidModel) : ℤ := let b2 := e.b_2; b2*b2 + 24*e.b_4

def c_6 (e : ValidModel) : ℤ := let b2 := e.b_2;
  -(b2 ^ 3) + 36*b2*(e.b_4) - 216*e.b_6

def j_inv (e : ValidModel ) : ℤ × ℕ := let c4_3 := e.c_4 ^ 3;
  let Δ := e.discr; let div := Int.gcd c4_3 Δ;
  ((if Δ > 0 then c4_3 else -c4_3) / div, Int.natAbs (Δ / div))

def tIso (r s t u : ℤ) (e : Model) : Model := {
  a1 := (e.a1 + 2*s) / u,
  a2 := (e.a2 - s*e.a1 + 3*r - s*s) / (u * u),
  a3 := (e.a3 + r*e.a1 + 2*t) / u ^ 3,
  a4 := (e.a4 - s*e.a3 + 2*r*e.a2 - (t+r*s)*e.a1 + 3*r*r - 2*s*t) / u ^ 4,
  a6 := (e.a6 + r*e.a4 + r*r*e.a2 + r*r*r - t*(e.a3 + t + r*e.a1)) / u ^ 6
  }

def p_divisibility (e : Model) (p : ℤ) :=
  Int.rem e.a1 p = 0 ∧ Int.rem e.a2 (p * p) = 0 ∧ Int.rem e.a3 (p ^ 3) = 0
  ∧ Int.rem e.a4 (p ^ 4) = 0 ∧ Int.rem e.a6 (p ^ 6) = 0

lemma tIso_000p (e : ValidModel) (p : ℤ) (pd : p_divisibility e.toModel p) :
  (tIso 0 0 0 p e.toModel).discr ≠ 0 := by
  let e' := tIso 0 0 0 p e.toModel;


theorem tIso_valid (r s t u : ℤ) (e : ValidModel) : (tIso r s t u e.toModel).discr ≠ 0 := by sorry

def tIsoV (r s t u : ℤ) (e : ValidModel) : ValidModel :=
  let e' := tIso r s t u e.toModel;
  { a1 := e'.a1, a2 := e'.a2, a3 := e'.a3, a4 := e'.a4, a6 := e'.a6,
    discr_non_zero := tIso_valid r s t u e }

def all_quantities (e : ValidModel) : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × (ℤ × ℕ) :=
  let (a1_2, a1a3, a3_2, a2x4) := (e.a1*e.a1, e.a1*e.a3, e.a3*e.a3, 4*e.a2);
  let (b2, b4, b6) := (a1_2 + a2x4, a1a3 + 2*e.a4, a3_2 + 4*e.a6);
  let b8 := (a1_2 + a2x4)*e.a6 - (a1a3 + e.a4)*e.a4 + e.a2*a3_2;
  let (b2_2, b2b4) := (b2 * b2, b2 * b4); let c4 := b2_2 - 24*b4;
  let Δ := -b2_2*b8 - 8*(b4 ^4) + (b2b4 - 3*b6)*b6*9;
  let c4_3 :=  e.c_4 ^ 3; let div := Int.gcd c4_3 Δ;
  (b2, b4, b6, b8, c4, -b2*b2_2 + 36*b2b4 - 216*b6, Δ,
  ((if Δ > 0 then c4_3 else -c4_3) / div, Int.natAbs (Δ / div)))

partial def count_valuation (v : ℕ) (p : ℤ) (x : ℤ) :=
  if p ∤ x then v else count_valuation (v + 1) p (x / p)
def valuation : ℤ → ℤ → ℕ := count_valuation 0

def cMod (x : ℤ) (p : ℤ) : ℤ :=
  let r := x % p; if 2*r > p then r - p else if 2*r <= -p then r + p else r

partial def euclide_descent (t r t' r' p : ℤ) : ℤ :=
  if r' ≠ 0 then let q := r / r'; euclide_descent t' r' (t-q*t') (r-q*r') p
  else cMod t p
def mod_inv (x : ℤ) (p : ℤ) := euclide_descent 0 p 1 x p

partial def count_parity (v : ℕ) (x : ℤ) :=
  if 2 ∤ x then (v, x) else count_parity (v + 1) (x / 2)
def parity : ℤ → (ℕ × ℤ) := count_parity 0

def kronecker_2 (x : ℕ) : ℤ := match x % 8 with
  | 1 => 1
  | 7 => 1
  | 3 => -1 | 5 => -1
  | _ => 0
partial def kronecker_odd (k a : ℤ) (b : ℕ) : ℤ :=
  -- b is odd and b > 0
  if a = 0 then if b > 1 then 0 else k else
  let (v2a, a') := parity a;
  let k' := if 2 ∣ v2a then k else k * (kronecker_2 b);
  let k'' := if a' % 4 = 3 ∧ b % 4 = 3 then k' else -k';
  let r := Int.natAbs a'; kronecker_odd k'' r (b % r)
def kronecker (a b : ℤ) : ℤ :=
  if b = 0 then if Int.natAbs a = 1 then 1 else 0 else
  if 2 ∣ b ∧ 2 ∣ a then 0 else
  let (v2b, b') := parity b;
  let k := if 2 ∣ v2b then 1 else kronecker_2 (Int.natAbs a);
  let k' := if b' < 0 ∧ a < 0 then -k else k;
  kronecker_odd k' a (Int.natAbs b')

def ex_root_quad (a b c p : ℤ) : Bool :=
  let (a', b', c') := (a % p, b % p, c % p);
  kronecker ((b' * b' - 4 * a' * c') % p) p = 1

unsafe def basic_decr_div (m mx my n : ℤ) (e: ValidModel) : ValidModel × ℕ × ℕ :=
  let (xa3, xa6) := (e.a3 / my, e.a6 / (mx * my));
  let (xa3_2, xa6_2) := (xa3 % 2, xa6 % 2);
  if 2 ∤ (xa3_2 * xa3_2 + 4 * xa6_2) then
    (e, Int.natAbs (n - m - 4), Int.natAbs m)
  else
    let e' := tIsoV 0 0 (my * xa6_2) 1 e;
    let (xa2, xa4, xa6) := (e'.a2 / 2, e'.a4 / (2 * mx), e'.a6 / (mx * my * 2));
    let (xa2_2, xa4_2, xa6_2) := (xa2 % 2, xa4 % 2, xa6 % 2);
    if 2 ∤ (xa4_2 * xa4_2 - 4 * xa2_2 * xa6_2) then
      (e', Int.natAbs (n - m - 5), Int.natAbs (m + 1))
    else
      let r := mx * (cMod (xa6_2 * xa2_2) 2);
      basic_decr_div (m + 2) (mx * 2) (my * 2) n (tIsoV r 0 0 1 e')

unsafe def basic_tate_algorithm (e: ValidModel) (p : ℤ) :=
  let (b2, b4, b6, _b8, c4, c6, dt, (jn, jd)) := all_quantities e;
  let (n, ordj) := (valuation p dt, if jn = 0 then 0 else valuation p jd);
  --(*Test for type I_0*)
  if n = 0 then (e, p, 0, 0, ordj, "I0") else
    --(*Change of coordinates s.t. p ∣ a3, a4, a6*)
    let inv2p := mod_inv 2 p;
    let (r, t) :=
      if p = 2 then
        if 2 ∣ b2 then (cMod e.a4 2, cMod (e.a4*(1+e.a2+e.a4) + e.a6) 2)
        else (cMod e.a3 2, cMod (e.a3+e.a4) 2)
      else if p = 3 then
        if 3 ∣ b2 then (cMod (-b6) 3, cMod (-e.a1*b6 + e.a3) 3)
        else (cMod (-b2*b4) 3, cMod (-e.a1*b2*b4 + e.a3) 3)
      else if p ∣ c4 then
        let r' := cMod (-(mod_inv 12 p)*b2) p;
        (r', -inv2p*(e.a1*r' + e.a3))
      else
        let r' := cMod (-(mod_inv (12*c4) p)*(c6 + b2*c4)) p;
        (r', -inv2p*(e.a1*r' + e.a3));
    let e1 := tIsoV r 0 t 1 e;
      let (b6, b8) := (e1.b_6, e1.b_8);
      --(*Tests for types In, II, III, IV*)
      if p ∤ c4 then
        (e1, p, 1, n, ordj, "I" ++ toString n)
      else let p2 := p*p;
      if p2 ∤ e1.a6 then (e1, p, n, n, ordj, "II")
      else let p3 := p2*p;
      if p3 ∤ b8 then (e1, p, n-1, n, ordj, "III")
      else if p3 ∤ b6 then
        (e1, p, n-2, n, ordj, "IV")
      else
        --(*Change of coordinates s.t. p ∣ a1, a2 and p2 ∣ a3 and p3 ∣ a6*)
        let (s, t) := if p = 2 then (cMod e1.a2 2, 2*(cMod (e1.a6/4) 2))
        else (-e1.a1*inv2p, -e1.a3*inv2p);
        let e2 := tIsoV 0 s t 1 e1;
          --(*Set up auxiliary cubic T3+bT2+cT+d*)
          let (b, c, d) := (e2.a2/p, e2.a4/p2, e2.a6/p3);
          let w := 27*d*d - b*b*c*c + 4*b*b*b*d - 18*b*c*d + 4*c*c*c;
          --(*Test for distinct roots: type I0* *)
          if p ∤ w then (e2, p, n-4, n, ordj, "I0*")
          else
            let x := 3*c-b*b;
            --(*Test for double root: type Im* *)
            if p ∤ x then
              --(*Change of coordinates s.t. the double root is T = 0*)
              let r := if p = 2 then c
              else if p = 3 then b*c else (b*c-9*d)*(mod_inv (2*x) p);
              --(*Make a3, a4, a6 repeatedly less divisible by p*)
              let e3 := tIsoV ((cMod r p)*p) 0 0 1 e2;
              let (e4, fp, m) := if p ≠ 2 then (e3, 2, n - 6)
              else basic_decr_div 1 p2 p2 n e3;
              (e4, p, fp, n, ordj, "I" ++ toString m ++ "*")
            else
              --(*Triple root case: types II*, III*, IV* or non-minimal*)
              --(*Change of coordinates s.t. the triple root is T=0*)
              let r := if p = 3 then -d else -b*(mod_inv 3 p);
              let e3 := tIsoV (p*(cMod r p)) 0 0 1 e2;
              let p4 := p3*p;
              let (x3, x6) := (e3.a3/p2, e3.a6/p4);
              --(*Test for type IV* *)
              if p ∤ (x3*x3 + 4*x6) then
                (e3, p, n-6, n, ordj, "IV*")
              else
                --(*Change of coordinates s.t. p3 ∣ a3 and p5 ∣ a6*)
                let t := if p = 2 then x6 else x3*inv2p;
                let e4 := tIsoV 0 0 (-p2*(cMod t p)) 1 e3;
                  --(*Tests for types III*, II* *)
                  if p4 ∤ e4.a4 then
                    (e4, p, n-7, n, ordj, "III*")
                  else
                    if (p4*p*p) ∣ e4.a6 then
                      (e4, p, n-8, n, ordj, "II*")
                    else
                      basic_tate_algorithm (tIsoV 0 0 0 p e4) p


def i67star : ValidModel := ⟨ ⟨0, -1, 0, -808051160, 9376500497392⟩ , by simp⟩

#eval basic_tate_algorithm i67star 2

end ValidModel
