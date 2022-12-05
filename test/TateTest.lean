import ECTate.Algebra.EllipticCurve.TateInt
import ECTate.Algebra.EllipticCurve.Model
import Mathlib.Data.Array.Defs
import Lean.Data.Parsec

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



-- section lmfdbmodel
-- open Lean Parsec

-- /--
--   Many arrays of `p` with the same size.
-- -/
-- partial def manyHomoCore (p : Parsec $ Array α) (acc : Array $ Array α) : Parsec $ Array $ Array α :=
--   (do
--     let first ← p
--     if acc.size = 0 then
--       manyCore p (acc.push first)
--     else
--       if acc.back.size = first.size then
--         manyCore p (acc.push first)
--       else
--         fail "expect same size"
--   )
--   <|> pure acc

-- /--
--   Many `p` separated by `s`.
-- -/
-- def manySep (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
--   manyCore (attempt (s *> p)) #[←p]

-- /--
--   Many arrays of `p` with the same size separated by `s`.
-- -/
-- def manySepHomo (p : Parsec $ Array α) (s : Parsec β) : Parsec $  Array $ Array α := do
--   manyHomoCore (attempt (s *> p)) #[←p]

-- /-
--   The following definitions are adapted from https://datatracker.ietf.org/doc/html/rfc4180
-- -/

-- def TEXTDATA : Parsec Char := satisfy fun c =>
--   0x20 ≤ c.val ∧ c.val ≤ 0x21 ∨
--   0x23 ≤ c.val ∧ c.val ≤ 0x2B ∨
--   0x2D ≤ c.val ∧ c.val ≤ 0x7E

-- def CR : Parsec Char := pchar '\r'
-- def LF : Parsec Char := pchar '\n'
-- def CRLF : Parsec String := pstring "\r\n"
-- def COMMA : Parsec Char := pchar ','
-- def DQUOTE : Parsec Char := pchar '\"'
-- def «2DQUOTE»  : Parsec Char := pstring "\"\"" *> pure '\"'

-- def escaped : Parsec String :=
--   DQUOTE *>
--   manyChars (TEXTDATA <|> COMMA <|> CR <|> LF <|> «2DQUOTE»)
--   <* DQUOTE

-- def «non-escaped» : Parsec String := manyChars TEXTDATA

-- def field : Parsec Field := escaped <|> «non-escaped»

-- def record : Parsec Record := manySep field COMMA

-- def file : Parsec $ Array Record := manySepHomo record (CRLF <* notFollowedBy eof) <* (optional CRLF) <* eof

-- def parse (s : String) : Except String $ Array $ Array $ String :=
--   match file s.mkIterator with
--   | Parsec.ParseResult.success _ res => Except.ok res
--   | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx.repr}: {err}"

-- end lmfdbmodel


def test (N : ℕ) : IO Unit := do
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
  print l.size
  let ma := min N l.size
  while n < ma do
    let str := l[n]!
  -- for str in l.zip (Array.range N) do
    let ⟨m, p, ok, of, oc, or⟩ : Model ℤ × ℕ × Kodaira × ℕ × ℕ × ℤ := parsefunc str
    -- if Δnz : m.discr ≠ 0 then
    match Int.tate_algorithm p sorry ⟨m, sorry⟩ with
    | (k, f, c, r, _, _, _, _) =>
      if (k, f, c) ≠ (ok, of, oc) ∨ or ≠ r.to_lmfdb then
        println str
        println (repr (k, f, c, r))
    n := n + 1
  println s!"{n}/{N} lines tested"

def main (N : List String) : IO Unit := test N[0]!.toNat!

#eval test 30
