import ECTate.Algebra.EllipticCurve.KodairaTypes
import ECTate.Algebra.EllipticCurve.Model
import Mathlib.Data.Int.Basic


open Kodaira

def kodaira_decode : ℤ → Kodaira
  | 0 => unreachable!
  | 1 => I 0
  | 2 => II
  | 3 => III
  | 4 => IV
  | -1 => Is 0
  | -2 => IIs
  | -3 => IIIs
  | -4 => IVs
  | n => if n > 0 then I (Int.natAbs (n - 4))
    else Is (Int.natAbs (-n - 4))

def parsefunc (s : String) : Model ℤ × ℕ × Kodaira × ℕ × ℕ × ℤ :=
  match String.split s (λ c => c = '{' || c = '}') with
  | "" :: mdl :: lcldata :: [] =>
    match String.split mdl (λ c => c = ',') with
    | [a1, a2, a3, a4, a6] =>
      match String.split lcldata (λ c => c = '&') with
      | ["", p, f, _, _, k, c, r] =>
        (⟨a1.toInt!, a2.toInt!, a3.toInt!, a4.toInt!, a6.toInt!⟩, p.toNat!, kodaira_decode k.toInt!, f.toNat!, c.toNat!, r.toInt!)
      | _ => unreachable!
    | _ => unreachable!
  | _ => unreachable!
