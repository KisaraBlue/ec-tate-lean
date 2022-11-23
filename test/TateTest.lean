import Init.System.IO
import ECTate.Algebra.EllipticCurve.TateInt
import ECTate.Algebra.EllipticCurve.Model
import Mathlib.Data.Array.Defs

open System
open IO
open FS

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


def test (N : ℕ) : IO Unit := do
  -- lines of the csv (which is ampersand separated) are
  -- model, p, conductor exponent f, disc exp, denom j exponent, kodaira type k, tamagawa c, reduction type]
  -- generated from the lmfdb with
  --  \copy (select ainvs, prime, conductor_valuation , discriminant_valuation, j_denominator_valuation, kodaira_symbol, tamagawa_number, reduction_type from ec_curvedata c inner join ec_localdata using ("lmfdb_label") order by c.conductor limit 300000) to 'test.csv' with delimiter as '&';
  let l ← lines $ mkFilePath ["test/lmfdb04.csv"]
  for str in l.zip (Array.range N) do
    let ⟨m, p, ok, of, oc, or⟩ : Model ℤ × ℕ × Kodaira × ℕ × ℕ × ℤ := parsefunc str.1
    -- if Δnz : m.discr ≠ 0 then
    match Int.tate_algorithm p sorry ⟨m, sorry⟩ with
    | (k, f, c, r, _, _, _, _) =>
      if (k, f, c) ≠ (ok, of, oc) ∨ or ≠ r.to_lmfdb then
        println str
        println (repr (k, f, c, r))
  println s!"{N} lines tested"

def main (N : List String) : IO Unit := test N[0]!.toNat!

#eval test 300
