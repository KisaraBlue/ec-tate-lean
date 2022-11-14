import ECTate.Algebra.EllipticCurve.TateInt

open IO Int
def main (args : List String) : IO UInt32 := do
  let p := args[0]!.toNat!
  let m := args.tail.map String.toInt!
  let v : ValidModel ℤ := ⟨⟨m[0]!, m[1]!, m[2]!, m[3]!, m[4]!⟩, sorry⟩
  println (repr (tate_algorithm p sorry v))
  pure 0
