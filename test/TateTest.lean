import Init.System.IO
import ECTate.Algebra.EllipticCurve.TateInt
import ECTate.Algebra.EllipticCurve.Model
import Mathlib.Data.Array.Defs

open System
open IO
open FS

open Kodaira

def kodaira_decode : ℤ → Kodaira
  | 0 => I 0 -- invalid code
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

def parsefunc (s : String) : Model ℤ × ℕ × Kodaira × ℕ × ℕ :=
  match String.split s (λ c => c = '{' || c = '}') with
  | "" :: mdl :: lcldata :: [] =>
    match String.split mdl (λ c => c = ',') with
    | [a1, a2, a3, a4, a6] =>
      match String.split lcldata (λ c => c = '&') with
      | ["", p, f, _, _, k, c, _] =>
        (⟨a1.toInt!, a2.toInt!, a3.toInt!, a4.toInt!, a6.toInt!⟩, p.toNat!, kodaira_decode k.toInt!, f.toNat!, c.toNat!)
      | _ => unreachable!
    | _ => unreachable!
  | _ => unreachable!


def test (N : ℕ) : IO Unit := do
  -- lines of the csv (which is ampersand separated are)
  -- model, p, conductor exponent f, disc exp, denom j exponent, kodaira type k, tamagawa c, root number]
  let l ← lines $ mkFilePath ["test/lmfdb.csv"]
  for str in l.zip (Array.range N) do
    let d : Model ℤ × ℕ × Kodaira × ℕ × ℕ := parsefunc str.1
    let m : Model ℤ := d.fst
    if Δnz : m.discr ≠ 0 then
      let p : ℕ := d.snd.fst; let res : Kodaira × ℕ × ℕ := d.snd.snd
      match Int.tate_algorithm p sorry ⟨m, Δnz⟩ with
      | (k, f, c, _, _, _, _) =>
        if (k, f, c) ≠ res then println str else print ""
    else
      print ""
  println (toString N ++ " lines tested")
  -- l.foldl (λ t h => do t; println h) (return ())
  -- parseFile <| FilePath.mk "board1.txt"

#eval test 3000
