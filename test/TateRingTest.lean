import ECTate.Algebra.EllipticCurve.TateRing
import ECTate.Algebra.EllipticCurve.Model
import Mathlib.Data.Array.Defs
import Lean.Data.Parsec
import test.LMFDB

open System
open IO
open FS


def testr (N : ℕ) : IO Unit := do
  -- lines of the csv (which is ampersand separated) are
  -- model, p, conductor exponent f, disc exp, denom j exponent, kodaira type k, tamagawa c, reduction type]
  -- generated from the lmfdb with
  --  \copy (select ainvs, prime, conductor_valuation , discriminant_valuation, j_denominator_valuation, kodaira_symbol, tamagawa_number, reduction_type from ec_curvedata c inner join ec_localdata using ("lmfdb_label") order by c.conductor limit 300000) to 'test.csv' with delimiter as '&';
  let mut n := 0

  let l := (← lines $ mkFilePath ["test/lmfdb00.csv"]) ++
           (← lines $ mkFilePath ["test/lmfdb01.csv"]) ++
           (← lines $ mkFilePath ["test/lmfdb02.csv"]) ++
           (← lines $ mkFilePath ["test/lmfdb03.csv"]) ++
           (← lines $ mkFilePath ["test/lmfdb04.csv"]) ++
           (← lines $ mkFilePath ["test/lmfdb05.csv"])
  println l.size
  let ma := min N l.size
  while n < ma do
    let str := l[n]!
  -- for str in l.zip (Array.range N) do
    let ⟨m, p, ok, of, oc, or⟩ : Model ℤ × ℕ × Kodaira × ℕ × ℕ × ℤ := parsefunc str
    -- if Δnz : m.discr ≠ 0 then
    match tate_algorithm (Int.primeEVR (sorry : Nat.Prime p)) ⟨m, sorry⟩ 1 0 0 0 with
    | (k, f, c, _, _, _, _) =>
      if (k, f, c) ≠ (ok, of, oc) then
        println str
        println (repr (k, f, c))
        println (repr (ok, of, oc))
    n := n + 1
  println s!"{n}/{N} lines tested"

def main (N : List String) : IO Unit := testr N[0]!.toNat!

#eval testr 100
