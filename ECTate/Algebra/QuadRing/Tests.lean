import ECTate.Algebra.EllipticCurve.Model
import ECTate.Algebra.QuadRing.Basic


-- Here we test that we can create elliptic curves over QuadRings
-- and at least calculate their discriminants

-- https://www.lmfdb.org/EllipticCurve/2.0.3.1/49.1/CMa/1

def cma1 : Model (QuadRing ℚ 1 (-1)) :=
⟨0,⟨1,1⟩,⟨0,1⟩,⟨0,1⟩,0⟩

#eval cma1.discr
