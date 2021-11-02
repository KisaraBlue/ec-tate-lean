import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.Basic

structure Model (R : Type u) [CommRing R] where
  a1 : R
  a2 : R
  a3 : R
  a4 : R
  a6 : R

variable {R : Type u} [CommRing R]

namespace Model

def b_2 (e : Model R) : R := e.a1 * e.a1 + 4 * e.a2

def b_4 (e : Model R) : R := e.a1 * e.a3 + 2 * e.a4

def b_6 (e : Model R) : R := e.a3 * e.a3 + 4 * e.a6

def b_8 (e : Model R) : R :=
  e.a1*e.a1*e.a6 - e.a1*e.a3*e.a4 + 4*e.a2*e.a6 + e.a2*e.a3*e.a3 - e.a4*e.a4

def discr (e : Model R) : R :=
  let (b2, b4, b6, b8) := (e.b_2, e.b_4, e.b_6, e.b_8);
  -b2*b2*b8 - 8*(b4 ^ 3) - 27*b6*b6 + 9*b2*b4*b6

--instance [Repr R] : Repr (Model R) := ⟨ λ (e : Model R) n => (repr _)⟩

end Model

structure ValidModel (R : Type u) [CommRing R] extends Model R where
  discr_non_zero : toModel.discr ≠ 0



namespace ValidModel

def discr (e : ValidModel R) : R := e.toModel.discr

def c_4 (e : ValidModel R) : R := let b2 := e.b_2; b2*b2 + 24*e.b_4

def c_6 (e : ValidModel R) : R := let b2 := e.b_2;
  -(b2 ^ 3) + 36*b2*(e.b_4) - 216*e.b_6

def j_inv (e : ValidModel ℤ) : ℤ × ℕ := let c4_3 := e.c_4 ^ 3;
  let Δ := e.discr; let div := Int.gcd c4_3 Δ;
  ((if Δ > 0 then c4_3 else -c4_3) / div, Int.natAbs (Δ / div))

def tIso (r s t u : ℤ) (e : Model ℤ) : Model ℤ := {
  a1 := (e.a1 + 2*s) / u,
  a2 := (e.a2 - s*e.a1 + 3*r - s*s) / (u * u),
  a3 := (e.a3 + r*e.a1 + 2*t) / u ^ 3,
  a4 := (e.a4 - s*e.a3 + 2*r*e.a2 - (t+r*s)*e.a1 + 3*r*r - 2*s*t) / u ^ 4,
  a6 := (e.a6 + r*e.a4 + r*r*e.a2 + r*r*r - t*(e.a3 + t + r*e.a1)) / u ^ 6
  }

def p_divisibility (e : Model ℤ) (p : ℤ) :=
  Int.rem e.a1 p = 0 ∧ Int.rem e.a2 (p * p) = 0 ∧ Int.rem e.a3 (p ^ 3) = 0
  ∧ Int.rem e.a4 (p ^ 4) = 0 ∧ Int.rem e.a6 (p ^ 6) = 0

lemma tIso_000p (e : ValidModel ℤ) (p : ℤ) (pd : p_divisibility e.toModel p) :
  (tIso 0 0 0 p e.toModel).discr ≠ 0 := by sorry

theorem tIso_valid (r s t u : ℤ) (e : ValidModel ℤ) : (tIso r s t u e.toModel).discr ≠ 0 := by sorry

def tIsoV (r s t u : ℤ) (e : ValidModel ℤ) : ValidModel ℤ :=
  let e' := tIso r s t u e.toModel;
  { a1 := e'.a1, a2 := e'.a2, a3 := e'.a3, a4 := e'.a4, a6 := e'.a6,
    discr_non_zero := tIso_valid r s t u e }

def all_quantities (e : ValidModel ℤ) : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × (ℤ × ℕ) :=
  let (a1_2, a1a3, a3_2, a2x4) := (e.a1*e.a1, e.a1*e.a3, e.a3*e.a3, 4*e.a2);
  let (b2, b4, b6) := (a1_2 + a2x4, a1a3 + 2*e.a4, a3_2 + 4*e.a6);
  let b8 := (a1_2 + a2x4)*e.a6 - (a1a3 + e.a4)*e.a4 + e.a2*a3_2;
  let (b2_2, b2b4) := (b2 * b2, b2 * b4); let c4 := b2_2 - 24*b4;
  let Δ := -b2_2*b8 - 8*(b4 ^4) + (b2b4 - 3*b6)*b6*9;
  let c4_3 :=  e.c_4 ^ 3; let div := Int.gcd c4_3 Δ;
  (b2, b4, b6, b8, c4, -b2*b2_2 + 36*b2b4 - 216*b6, Δ,
  ((if Δ > 0 then c4_3 else -c4_3) / div, Int.natAbs (Δ / div)))

partial def count_valuation (v : ℕ) (p : ℤ) (x : ℤ) :=
  if x % p ≠ 0 then v else count_valuation (v + 1) p (x / p)
def valuation : ℤ → ℤ → ℕ := count_valuation 0

def center_mod (x : ℤ) (p : ℤ) : ℤ :=
  let r := x % p; if 2*r > p then r - p else if 2*r <= -p then r + p else r

partial def euclide_descent (t r t' r' p : ℤ) : ℤ :=
  if r' ≠ 0 then let q := r / r'; euclide_descent t' r' (t-q*t') (r-q*r') p
  else center_mod t p
def mod_inv (x : ℤ) (p : ℤ) := euclide_descent 0 p 1 x p

partial def count_parity (v : ℕ) (x : ℤ) :=
  if x % 2 ≠ 0 then (v, x) else count_parity (v + 1) (x / 2)
def parity : ℤ → (ℕ × ℤ) := count_parity 0

def kronecker_2 (x : ℕ) : ℤ := match x % 8 with
  | 1 => 1 | 7 => 1
  | 3 => -1 | 5 => -1
  | _ => 0
partial def kronecker_odd (k a : ℤ) (b : ℕ) : ℤ :=
  -- b is odd and b > 0
  if a = 0 then if b > 1 then 0 else k else
  let (v2a, a') := parity a;
  let k' := if v2a % 2 = 0 then k else k * (kronecker_2 b);
  let k'' := if a' % 4 = 3 ∧ b % 4 = 3 then k' else -k';
  let r := Int.natAbs a'; kronecker_odd k'' r (b % r)
def kronecker (a b : ℤ) : ℤ :=
  if b = 0 then if Int.natAbs a = 1 then 1 else 0 else
  if b % 2 = 0 ∧ a % 2 = 0 then 0 else
  let (v2b, b') := parity b;
  let k := if v2b % 2 = 0 then 1 else kronecker_2 (Int.natAbs a);
  let k' := if b' < 0 ∧ a < 0 then -k else k;
  kronecker_odd k' a (Int.natAbs b')

def ex_root_quad (a b c p : ℤ) : Bool :=
  let (a', b', c') := (a % p, b % p, c % p);
  kronecker ((b' * b' - 4 * a' * c') % p) p = 1

-- ask Alex why partial doesn't work here
unsafe def basic_incr_div (m mx my n : ℤ) (e: ValidModel ℤ) : ValidModel ℤ × ℕ × ℕ :=
  let (xa3, xa6) := (e.a3 / my, e.a6 / (mx * my));
  let (xa3_2, xa6_2) := (xa3 % 2, xa6 % 2);
  if (xa3_2 * xa3_2 + 4 * xa6_2) % 2 ≠ 0 then
    (e, Int.natAbs (n - m - 4), Int.natAbs m)
  else
    let e' := tIsoV 0 0 (my * xa6) 1 e;
    let (xa2, xa4, xa6) := (e'.a2 / 2, e'.a4 / (2 * mx), e'.a6 / (mx * my * 2));
    let (xa2_2, xa4_2, xa6_2) := (xa2 % 2, xa4 % 2, xa6 % 2);
    if (xa4_2 * xa4_2 - 4 * xa2_2 * xa6_2) % 2 ≠ 0 then
      (e', Int.natAbs (n - m - 5), Int.natAbs (m + 1))
    else
      let r := mx * (center_mod (xa6_2 * xa2_2) 2);
      basic_incr_div (m + 2) (mx * 2) (my * 2) n (tIsoV r 0 0 1 e')

unsafe def basic_tate_algorithm (e: ValidModel ℤ) (p : ℤ) :=
  let (b2, b4, b6, _b8, c4, c6, dt, (jn, jd)) := all_quantities e;
  let n := valuation p dt;
  let ordj := if jn = 0 then 0 else valuation p jd;
  --(*Test for type I_0*)
  if n = 0 then (e, p, 0, 0, ordj, "I0 ") else
    --(*Change of coordinates s.t. p | a3, a4, a6*)
    let inv2p := mod_inv 2 p;
    let (r, t) :=
      if p = 2 then
        if b2 % 2 = 0 then (center_mod e.a4 2, center_mod (e.a4*(1+e.a2+e.a4) + e.a6) 2)
        else (center_mod e.a3 2, center_mod (e.a3+e.a4) 2)
      else if p = 3 then
        if b2 % 3 = 0 then (center_mod (-b6) 3, center_mod (-e.a1*b6 + e.a3) 3)
        else (center_mod (-b2*b4) 3, center_mod (-e.a1*b2*b4 + e.a3) 3)
      else if c4 % p = 0 then
        let r' := center_mod (-(mod_inv 12 p)*b2) p;
        (r', -inv2p*(e.a1*r' + e.a3))
      else
        let r' := center_mod (-(mod_inv (12*c4) p)*(c6 + b2*c4)) p;
        (r', -inv2p*(e.a1*r' + e.a3))
        ;
    let e1 := tIsoV r 0 t 1 e;
      let (b6, b8) := (e1.b_6, e1.b_8);
      --(*Tests for types In, II, III, IV*)
      if c4 % p ≠ 0 then
        (e1, p, 1, n, ordj, "I" ++ toString n)
      else let p2 := p*p;
      if e1.a6 % p2 ≠ 0 then (e1, p, n, n, ordj, "II  ")
      else let p3 := p2*p;
      if b8 % p3 ≠ 0 then (e1, p, n-1, n, ordj, "III ")
      else if b6 % p3 ≠ 0 then
        (e1, p, n-2, n, ordj, "IV  ")
      else
        --(*Change of coordinates s.t. p | a1, a2 and p2 | a3 and p3 | a6*)
        let (s, t) := if p = 2 then (center_mod e1.a2 2, 2*(center_mod (e1.a6/4) 2))
        else (-e1.a1*inv2p, -e1.a3*inv2p);
        let e2 := tIsoV 0 s t 1 e1;
          --(*Set up auxiliary cubic T3+bT2+cT+d*)
          let (b, c, d) := (e2.a2/p, e2.a4/p2, e2.a6/p3);
          let w := 27*d*d - b*b*c*c + 4*b*b*b*d - 18*b*c*d + 4*c*c*c;
          --(*Test for distinct roots: type I0* *)
          if w % p ≠ 0 then (e2, p, n-4, n, ordj, "I0* ")
          else
            let x := 3*c-b*b;
            --(*Test for double root: type Im* *)
            if x % p ≠ 0 then
              --(*Change of coordinates s.t. the double root is T = 0*)
              let r := if p = 2 then c
              else if p = 3 then b*c else (b*c-9*d)*(mod_inv (2*x) p);
              --(*Make a3, a4, a6 repeatedly more divisible by p*)
              let e3 := tIsoV ((center_mod r p)*p) 0 0 1 e2;
              let (e4, fp, m) := if p ≠ 2 then (e3, 2, n - 6)
              else basic_incr_div 1 p2 p2 n e3;
              (e4, p, fp, n, ordj, "I" ++ toString m ++ "*")
            else
              --(*Triple root case: types II*, III*, IV* or non-minimal*)
              --(*Change of coordinates s.t. the triple root is T=0*)
              let r := if p = 3 then -d else -b*(mod_inv 3 p);
              let e3 := tIsoV (p*(center_mod r p)) 0 0 1 e2;
              let p4 := p3*p;
              let (x3, x6) := (e3.a3/p2, e3.a6/p4);
              --(*Test for type IV* *)
              if (x3*x3 + 4*x6) % p ≠ 0 then
                (e3, p, n-6, n, ordj, "IV* ")
              else
                --(*Change of coordinates s.t. p3 | a3 and p5 | a6*)
                let t := if p = 2 then x6 else x3*inv2p;
                let e4 := tIsoV 0 0 (-p2*(center_mod t p)) 1 e3;
                  --(*Tests for types III*, II* *)
                  if e4.a4 % p4 ≠ 0 then
                    (e4, p, n-7, n, ordj, "III*")
                  else
                    if e4.a6 % (p4*p*p) ≠ 0 then
                      (e4, p, n-8, n, ordj, "II* ")
                    else
                      basic_tate_algorithm (tIsoV 0 0 0 p e4) p

def i67star : ValidModel ℤ := ⟨⟨ 0,-1,0,-808051160,9376500497392⟩ , sorry⟩


end ValidModel
