import Init.System.IO
import Mathlib.Algebra.EllipticCurve.TateInt
import Mathlib.Algebra.EllipticCurve.Model
import Mathlib.Data.Array.Defs

open System
open IO
open FS

open Kodaira


#eval String.split "SEDTSYKJGYOUGYSGAUFYIT" (λ c => c = 'S')

#check "{0,-1,0,-808051160,9376500497392}&2&4&75&63&-71&2&0"
#eval String.toInt! "-7846513"

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
      | ["", p, f, n, j, k, c, _] =>
        (⟨a1.toInt!, a2.toInt!, a3.toInt!, a4.toInt!, a6.toInt!⟩, p.toNat!, kodaira_decode k.toInt!, f.toNat!, c.toNat!)
      | _ => (⟨0,0,0,0,0⟩,0,I 0,0,0)
    | _ => (⟨0,0,0,0,0⟩,0,I 0,0,0)
  | _ => (⟨0,0,0,0,0⟩,0,I 0,0,0)


unsafe
def test (N : ℕ) : IO Unit := do
  let l ← lines $ mkFilePath ["test/lmfdb.csv"]
  let limit : ℕ := min l.size N
  for i in Array.range limit do
    let str : String := l[i]
    let d : Model ℤ × ℕ × Kodaira × ℕ × ℕ := parsefunc str
    let m : Model ℤ := d.fst
    if Δnz : m.discr ≠ 0 then
      let p : ℕ := d.snd.fst; let res : Kodaira × ℕ × ℕ := d.snd.snd
      match Int.tate_algorithm p sorry ⟨m, Δnz⟩ with
      | (k, f, c, _, _, _, _) =>
        if (k, f, c) ≠ res then println str else print ""
        if i = limit - 1 then println "All lines tested"
    else
      print ""
  -- l.foldl (λ t h => do t; println h) (return ())
  -- parseFile <| FilePath.mk "board1.txt"

#eval test 300000
