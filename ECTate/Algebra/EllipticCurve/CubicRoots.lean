import ECTate.Algebra.Ring.Basic
import Mathlib.Algebra.CharP.Two
import ECTate.FieldTheory.PerfectClosure
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.PrintPrefix
import Mathlib.Tactic.LibrarySearch
import Mathlib.Util.WhatsNew
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.Algebra.EuclideanDomain.Basic


namespace Mathlib
open Lean hiding Rat mkRat
open Meta

namespace Meta.NormNum
open Qq
-- TODO move to mathlib next to mod

theorem isNat_natDiv : {a b : ℕ} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.div a' b' = c → IsNat (a / b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by aesop⟩

/-- The `norm_num` extension which identifies expressions of the form `Nat.div a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℕ) % _, HDiv.hDiv (_ : ℕ) _, Nat.div _ _] def evalNatDiv :
    NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℕ))) (b : Q(ℕ)) ← whnfR e | failure
  -- We trust that the default instance for `HDiv` is `Nat.div` when the first parameter is `ℕ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := ℕ))
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨na, pa⟩ ← deriveNat a sℕ; let ⟨nb, pb⟩ ← deriveNat b sℕ
  have pa : Q(IsNat $a $na) := pa
  have pb : Q(IsNat $b $nb) := pb
  have nc : Q(ℕ) := mkRawNatLit (na.natLit! / nb.natLit!)
  let r : Q(Nat.div $na $nb = $nc) := (q(Eq.refl $nc) : Expr)
  return (.isNat sℕ nc q(isNat_natDiv $pa $pb $r) : Result q($a / $b))
end Meta.NormNum
end Mathlib


namespace Field
variable {K : Type u} [Field K]

variable (a b c : K)
@[simp]
def cubic_discr : K := a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2
@[simp]
def cubic_triple_discr₁ : K := 9 * c - a * b
@[simp]
def cubic_triple_discr₂ (a b c : K) : K := a ^ 2 - 3 * b
@[simp]
def cubic_triple_discr₃ : K := b ^ 2 - 3 * a * c

open PerfectRing
@[simp]
noncomputable
def cubic_double_root [PerfectRing K] : K :=
match ringChar K with
| 2 => pth_root b
| 3 => b / a
| _ =>
  cubic_triple_discr₁ a b c / (2 * cubic_triple_discr₂ a b c)
@[simp]
def cubic_eval (x : K) : K := x ^ 3 + a * x ^ 2 + b * x + c
@[simp]
def cubic_partial_eval (a b c x : K) : K := 3 * x ^ 2 + 2 * a * x + b
@[simp]
def cubic_partial_partial_eval (a b c x : K) : K := 6 * x + 2 * a

@[simp]
noncomputable
def cubic_triple_root [PerfectRing K] (a b c : K) : K :=
match ringChar K with
| 2 => a
| 3 => - pth_root c
| _ => -a / 3

lemma cubic_double_root_is_root_of_discr_eq_zero [PerfectRing K] (h : cubic_triple_discr₂ a b c ≠ 0)
  (hd : cubic_discr a b c = 0) :
  cubic_eval a b c (cubic_double_root a b c) = 0 :=
by
  simp only [cubic_discr] at hd
  simp only [cubic_eval, cubic_double_root, cubic_triple_discr₁, ne_eq, neg_sub, cubic_triple_discr₂, ite_not,
    ite_pow, div_pow, mul_ite]
  split
  . rename_i heq
    have : CharP K 2
    sorry
    simp at hd
    rw [pth_root_pow_eq (n := 2), heq]
    rw [pth_root_pow_eq, heq]
    -- simp -- TODO norm_num doesn't turn raw nat lits into ofNat
    norm_num
    rw [← Nat.cast_ofNat (R := K), ← Nat.cast_ofNat (R := K),
      ← Nat.cast_ofNat (R := K),
      ← Nat.mod_add_div 4 (ringChar K),
      ← Nat.mod_add_div 18 (ringChar K),
      ← Nat.mod_add_div 27 (ringChar K)] at hd
    simp [heq] at hd
    norm_num [heq] at hd -- TODO doesn't work without passing on heq on previous line
    abel_nf
    rw [← Nat.cast_ofNat (R := ℤ), ← Nat.mod_add_div 2 (ringChar K)]
    simp
    simp [heq] -- TODO why no nat mod self fires
    sorry

  . rename_i heq
    by_cases ha : a = 0
    . simp [ha, not_or] at *
      sorry
    field_simp
    simp at hd
    -- simp -- TODO norm_num doesn't turn raw nat lits into ofNat
    norm_num
    rw [← Nat.cast_ofNat (R := K), ← Nat.cast_ofNat (R := K),
      ← Nat.cast_ofNat (R := K),
      ← Nat.mod_add_div 4 (ringChar K),
      ← Nat.mod_add_div 18 (ringChar K),
      ← Nat.mod_add_div 27 (ringChar K)] at hd
    simp at hd
    simp [heq] at hd
    norm_num [heq] at hd -- TODO doesn't work without passing on heq on previous line
    convert_to -(a ^ 2 * b ^ 2 - a ^ 3 * c - b ^ 3) * a ^ 3 = 0
    . ring_nf
      sorry

    simp [hd]

  . rename_i hh
    simp only [cubic_triple_discr₂] at h
    have : 2 * (a ^ 2 - 3 * b) ≠ 0
    . simp
      rintro (hl | hr)
      . sorry --library_search
      . contradiction
    field_simp
    convert_to
      8 * (-a^2 + 3*b)^3 * (2*a^3 - 9*a*b + 27*c) * (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2)
      = 0
    . ring
    simp [hd]

  -- . rw [cubic_triple_discr₂] at h
  --   have : 2 ()
  --   field_simp
  --   rw [(show (((2 * b ^ 2 - 6 * a * c) ^ 3 * (9 * c - a * b) ^ 2 + a * (2 * b ^ 2 - 6 * a * c) ^ 2 * (9 * c - a * b) ^ 3) *
  --               (9 * c - a * b) +
  --             b * (2 * b ^ 2 - 6 * a * c) * ((9 * c - a * b) ^ 3 * (9 * c - a * b) ^ 2) +
  --           c * ((9 * c - a * b) ^ 3 * (9 * c - a * b) ^ 2 * (9 * c - a * b))) = (a*b - 9*c)^3 *
  --       (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2) * (2*b^3 - 9*a*b*c + 27*c^2) by ring), hd]
  --   simp

lemma cubic_double_root_is_double_root_of_discr_eq_zero [PerfectRing K]
  (h : cubic_triple_discr₂ a b c ≠ 0)
  (hd : cubic_discr a b c = 0) :
  cubic_partial_eval a b c (cubic_double_root a b c) = 0 :=
by
  simp only [cubic_discr] at hd
  simp only [cubic_partial_eval, cubic_double_root, cubic_triple_discr₁, ne_eq, neg_sub, cubic_triple_discr₂,
    ite_not, ite_pow, div_pow, mul_ite]
  split
  . rename_i hh
    -- cases h
    -- . rename_i h₁
    --   simp at h₁
    --   contradiction
    rename_i h₂
    simp only [cubic_triple_discr₂] at h₂
    field_simp -- todo field simp is ecsessive
    sorry
    -- convert_to
    --   -(16*a^5-96*a^3*b+144*a*b^2)*(9*c-a*b)
    --   +(-18*a^2+54*b)*(a ^ 2 * b ^ 2 - 4 * a ^ 3 * c - 4 * b ^ 3 + 18 * a * b * c - 27 * c ^ 2) = 0
    -- . ring
    -- rw [hh, hd]
    -- simp

  . field_simp
    sorry
    -- rw [(show
    --   3 * (2 * b ^ 2 - 6 * a * c) ^ 2 * (9 * c - a * b) + 2 * a * (2 * b ^ 2 - 6 * a * c) * (9 * c - a * b) ^ 2 +
    --        b * ((9 * c - a * b) ^ 2 * (9 * c - a * b)) =
    --   3 * b * (a*b - 9*c) * (a ^ 2 * b ^ 2 - 4 * a ^ 3 * c - 4 * b ^ 3 + 18 * a * b * c - 27 * c ^ 2)
    --   by ring), hd]
    -- simp
  . sorry

lemma cubic_triple_root_is_root_of_discr_eq_zero [PerfectRing K] -- (h₁ : cubic_triple_discr₁ a b c = 0)
  (h₂ : cubic_triple_discr₂ a b c = 0)
  -- (h₃ : cubic_triple_discr₃ a b c = 0)
  (hd : cubic_discr a b c = 0) :
  cubic_eval a b c (cubic_triple_root a b c) = 0 :=
by
  simp at hd --h₁ h₂ h₃
  simp
  split
  . rename_i hchar
    simp at *
    -- rw [← hchar] at h₂ h₃
    have h2 : (2 : K) = 0
    sorry
    have h4 : (4 : K) = 0
    sorry
    have h18 : (18 : K) = 0
    sorry
    have h27 : (27 : K) = 1
    sorry
    ring_nf
    simp [h4, h18, h27] at hd
    simp [h2]
    sorry
  . rename_i hchar
    simp at *
    -- rw [← hchar] at h₂ h₃
    have ha : a = 0
    sorry
    have hb : b = 0
    sorry
    rw [← hchar]
    simp only [ha, zero_mul, add_zero, hb, neg_zero]
    rw [neg_pow, pth_root_pow_char, hchar]
    . norm_num
    . rw [hchar]
      norm_num
  . have : (3 : K) ≠ 0
    sorry
    field_simp
    ring_nf
    -- rw [(show -(a * b * 243) + a ^ 3 * 54 + c * 729 = 27*a*(cubic_triple_discr₂ a b c) + 81*(cubic_triple_discr₁ a b c) by simp; ring)]
    sorry
    -- rw [h₂, h₁]
    -- simp


lemma cubic_triple_root_is_double_root_of_discr_eq_zero [PerfectRing K] (h₁ : cubic_triple_discr₁ a b c = 0)
  (h₂ : cubic_triple_discr₂ a b c = 0)
  -- (h₃ : cubic_triple_discr₃ a b c = 0)
  (hd : cubic_discr a b c = 0) :
  cubic_partial_eval a b c (cubic_triple_root a b c) = 0 :=
by
  simp at hd --h₁ h₂ h₃
  simp
  split
  . rename_i hchar
    simp at *
    -- rw [← hchar] at h₂ h₃
    have ha : a = 0
    sorry
    have hb : b = 0
    sorry
    have : (3 : K) = 0
    sorry
    simp [ha, zero_mul, add_zero, hb, neg_zero, this]
  . have : (3 : K) ≠ 0
    sorry
    field_simp
    ring_nf
    -- rw [(show -(a * b * 243) + a ^ 3 * 54 + c * 729 = 27*a*(cubic_triple_discr₂ a b c) + 81*(cubic_triple_discr₁ a b c) by simp; ring)]
    -- rw [h₂, h₁]
    -- simp
    sorry
  . sorry



/-
julia
+(base) alex:~ 🐌 julia
u               _
   _       _ _(_)_     |  Documentation: https://docs.julialang.org
  (_)     | (_) (_)    |
   _ _   _| |_  __ _   |  Type "?" for help, "]?" for Pkg help.
  | | | | | | |/ _` |  |
  | | |_| | | | (_| |  |  Version 1.8.5 (2023-01-08)
 _/ |\__'_|_|_|\__'_|  |  Official https://julialang.org/ release
|__/                   |

julia> using Singular
Singular.jl, based on
                     SINGULAR                               /
 A Computer Algebra System for Polynomial Computations     /  Singular.jl: 0.16.1
                                                         0<   Singular   : 4.3.1p2
 by: W. Decker, G.-M. Greuel, G. Pfister, H. Schoenemann   \
FB Mathematik der Universitaet, D-67653 Kaiserslautern      \


julia> R, (x, y, t) = PolynomialRing(QQ, ["x", "y", "t"])
(Singular Polynomial Ring (QQ),(x,y,t),(dp(3),C), spoly{n_Q}[x, y, t])

julia> I = Ideal(R, x - t^2, y - t^3)
Singular ideal over Singular Polynomial Ring (QQ),(x,y,t),(dp(3),C) with generators (-t^2 + x, -t^3 + y)

julia> J = eliminate(I, t)
Singular ideal over Singular Polynomial Ring (QQ),(x,y,t),(dp(3),C) with generators (x^3 - y^2)

julia> R, (a, b, c, x) = PolynomialRing(QQ, ["a", "b", "c", "x"])
(Singular Polynomial Ring (QQ),(a,b,c,x),(dp(4),C), spoly{n_Q}[a, b, c, x])

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x),(dp(4),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b)

julia> J = eliminate(I, x)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x),(dp(4),C) with generators (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2)

julia> R, (a, b, c, x, t, s) = PolynomialRing(QQ, ["a", "b", "c", "x", "t", "s"])
(Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C), spoly{n_Q}[a, b, c, x, t, s])

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s)])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c)

julia> J = eliminate(I, x)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a + 3*t - s, 3*t^2 - 2*t*s - b, 2*t*s^2 - 3*b*t + b*s - 9*c, b*t*s - b^2 - 9*c*t + 6*c*s, b^2*t - b^2*s - 6*c*t*s + 4*c*s^2 + 3*b*c, b^2*s^2 - 4*c*s^3 - b^3 + 27*c^2)

julia> R, (a, b, c, x, t, s) = PolynomialRing(ZZ, ["a", "b", "c", "x", "t", "s"])
(Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), spoly{n_Z}[a, b, c, x, t, s])

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b)

julia> J = eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s)])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c)

julia> J = eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a + 3*t - s, 3*t^2 - 2*t*s - b, 2*t*s^2 - 3*b*t + b*s - 9*c, t^2*s - b*t - 3*c, b*t*s - b^2 - 9*c*t + 6*c*s, t^3 - t^2*s + c, b*t^2 - b^2 - 6*c*t + 4*c*s, b^2*t - b^2*s - 6*c*t*s + 4*c*s^2 + 3*b*c, b^2*s^2 - 4*c*s^3 - b^3 + 27*c^2)

julia> J = eliminate(I, [x, a])
ERROR: MethodError: no method matching eliminate(::sideal{spoly{n_Z}}, ::Vector{spoly{n_Z}})
Closest candidates are:
  eliminate(::sideal{S}, ::S...) where {T<:AbstractAlgebra.RingElem, S<:Union{spluralg{T}, spoly{T}}} at ~/.julia/packages/Singular/zLgw5/src/ideal/ideal.jl:679
Stacktrace:
 [1] top-level scope
   @ REPL[16]:1

julia> J = eliminate(eliminate(I, x), a)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (3*t^2 - 2*t*s - b, 2*t*s^2 - 3*b*t + b*s - 9*c, t^2*s - b*t - 3*c, b*t*s - b^2 - 9*c*t + 6*c*s, t^3 - b*t - 2*c, b*t^2 - b^2 - 6*c*t + 4*c*s, b^2*t - b^2*s - 6*c*t*s + 4*c*s^2 + 3*b*c, b^2*s^2 - 4*c*s^3 - b^3 + 27*c^2)

julia> J = eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a^2 - s^2 - 3*b, 2*a*s^2 - 2*s^3 - 3*a*b + 27*c, a*b*s - b*s^2 + 3*b^2 - 9*a*c - 9*c*s, a*b^2 + 2*b^2*s - 6*a*c*s - 6*c*s^2 - 9*b*c, b^2*s^2 - 4*c*s^3 - b^3 + 27*c^2)

julia> J = eliminate(eliminate(eliminate(I, x), t), s)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2)

julia> J = eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*a*t + 3*t^2 + b, t^3 - b*t - 2*c, b*t^2 - b^2 + 4*a*c + 6*c*t, a*t^2 + 3*t^3 - b*t - 3*c, a*b*t + 2*b^2 - 6*a*c - 9*c*t, a*b^2 - 4*a^2*c + 2*b^2*t + 9*c*t^2 + 6*b*c)

julia> J = eliminate(eliminate(eliminate(I, x), t), s)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2)

julia> (-36 a^4 b c^2 + 17 a^3 b^3 c + 108 a^3 c^3 - 2 a^2 b^5 + 135 a^2 b^2 c^2 - 72 a b^4 c - 729 a b c^3 + 8 b^6 + 162 b^3 c^2 + 729 c^4) in eliminate(eliminate(eliminate(I, x), t), s)
ERROR: syntax: missing comma or ) in argument list
Stacktrace:
 [1] top-level scope
   @ none:1

julia> (-36 *a^4 *b* c^2 + 17 *a^3* b^3* c + 108 *a^3* c^3 - 2 *a^2* b^5 + 135 *a^2* b^2 *c^2 - 72* a* b^4 *c - 729 *a8 b* c^3 + 8* b^6 + 162* b^3* c^2 + 729 *c^4) in eliminate(eliminate(eliminate(I, x), t), s)
ERROR: syntax: missing comma or ) in argument list
Stacktrace:
 [1] top-level scope
   @ none:1

julia> (-36 *a^4 *b* c^2 + 17 *a^3* b^3* c + 108 *a^3* c^3 - 2 *a^2* b^5 + 135 *a^2* b^2 *c^2 - 72* a* b^4 *c - 729 *a8 b* c^3 + 8* b^6 + 162* b^3* c^2 + 729 *c^4)
ERROR: syntax: missing comma or ) in argument list
Stacktrace:
 [1] top-level scope
   @ none:1

julia> -36 *a^4 *b* c^2 + 17 *a^3* b^3* c + 108 *a^3* c^3 - 2 *a^2* b^5 + 135 *a^2* b^2 *c^2 - 72* a* b^4 *c - 729 *a8 b* c^3 + 8* b^6 + 162* b^3* c^2 + 729 *c^4
ERROR: syntax: extra token "b" after end of expression
Stacktrace:
 [1] top-level scope
   @ none:1

julia> -36 *a^4 *b* c^2 + 17 *a^3* b^3* c + 108 *a^3* c^3 - 2 *a^2* b^5 + 135 *a^2* b^2 *c^2 - 72* a* b^4 *c - 729 *a8 b* c^3 + 8* b^6 + 162* b^3* c^2 + 729 *c^4
ERROR: syntax: extra token "b" after end of expression
Stacktrace:
 [1] top-level scope
   @ none:1

julia> -36 *a^4 *b* c^2 + 17 *a^3* b^3* c + 108 *a^3* c^3 - 2 *a^2* b^5 + 135 *a^2* b^2 *c^2 - 72* a* b^4 *c - 729 *a* b* c^3 + 8* b^6 + 162* b^3* c^2 + 729 *c^4
-2*a^2*b^5 + 17*a^3*b^3*c - 36*a^4*b*c^2 + 8*b^6 - 72*a*b^4*c + 135*a^2*b^2*c^2 + 108*a^3*c^3 + 162*b^3*c^2 - 729*a*b*c^3 + 729*c^4

julia> _
ERROR: all-underscore identifier used as rvalue
Stacktrace:
 [1] top-level scope
   @ REPL[27]:1

julia> -36 *a^4 *b* c^2 + 17 *a^3* b^3* c + 108 *a^3* c^3 - 2 *a^2* b^5 + 135 *a^2* b^2 *c^2 - 72* a* b^4 *c - 729 *a* b* c^3 + 8* b^6 + 162* b^3* c^2 + 729 *c^4
-2*a^2*b^5 + 17*a^3*b^3*c - 36*a^4*b*c^2 + 8*b^6 - 72*a*b^4*c + 135*a^2*b^2*c^2 + 108*a^3*c^3 + 162*b^3*c^2 - 729*a*b*c^3 + 729*c^4

julia> ans in eliminate(eliminate(eliminate(I, x), t), s)
ERROR: MethodError: no method matching iterate(::sideal{spoly{n_Z}})
Closest candidates are:
  iterate(::Union{LinRange, StepRangeLen}) at range.jl:872
  iterate(::Union{LinRange, StepRangeLen}, ::Integer) at range.jl:872
  iterate(::T) where T<:Union{Base.KeySet{<:Any, <:Dict}, Base.ValueIterator{<:Dict}} at dict.jl:712
  ...
Stacktrace:
 [1] in(x::spoly{n_Z}, itr::sideal{spoly{n_Z}})
   @ Base ./operators.jl:1242
 [2] top-level scope
   @ REPL[29]:1

julia> -36 *a^4 *b* c^2 + 17 *a^3* b^3* c + 108 *a^3* c^3 - 2 *a^2* b^5 + 135 *a^2* b^2 *c^2 - 72* a* b^4 *c - 729 *a* b* c^3 + 8* b^6 + 162* b^3* c^2 + 729 *c^4
-2*a^2*b^5 + 17*a^3*b^3*c - 36*a^4*b*c^2 + 8*b^6 - 72*a*b^4*c + 135*a^2*b^2*c^2 + 108*a^3*c^3 + 162*b^3*c^2 - 729*a*b*c^3 + 729*c^4

julia> factor(-36 *a^4 *b* c^2 + 17 *a^3* b^3* c + 108 *a^3* c^3 - 2 *a^2* b^5 + 135 *a^2* b^2 *c^2 - 72* a* b^4 *c - 729 *a* b* c^3 + 8* b^6 + 162* b^3* c^2 + 729 *c^4)
1 * (-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2) * (2*b^3 - 9*a*b*c + 27*c^2)

julia> ideal(R, [-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2, a^2*b +9a*c - 6*b^2])
ERROR: syntax: missing separator in array expression
Stacktrace:
 [1] top-level scope
   @ none:1

julia> ideal(R, [-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2, a^2*b +9*a*c - 6*b^2])
ERROR: syntax: missing separator in array expression
Stacktrace:
 [1] top-level scope
   @ none:1

julia>

julia> Ideal(R, [-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2, a^2*b +9*a*c - 6*b^2])
ERROR: syntax: missing separator in array expression
Stacktrace:
 [1] top-level scope
   @ none:1

julia> Ideal(R, [-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2, a^2*b + 9*a*c - 6*b^2])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2, a^2*b - 6*b^2 + 9*a*c)

julia>

julia> eliminate(Ideal(R, [-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2, a^2*b + 9*a*c - 6*b^2]), b)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (4*a^9*c - 324*a^6*c^2 + 8748*a^3*c^3 - 78732*c^4)

julia> eliminate(Ideal(R, [-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2, a^2*b + 9*a*c - 6*b^2]), a)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (4*b^9 - 324*b^6*c^2 + 8748*b^3*c^4 - 78732*c^6)

julia> eliminate(Ideal(R, [-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2, a^2*b + 9*a*c - 6*b^2]), c)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (4*a^6*b - 36*a^4*b^2 + 108*a^2*b^3 - 108*b^4)

julia>

julia>

julia> factor(((2 * b ^ 2 - 6 * a * c) ^ 3 * (9 * c - a * b) ^ 2 + a * (2 * b ^ 2 - 6 * a * c) ^ 2 * (9 * c - a * b) ^ 3) *
               (9 * c - a * b) +
             b * (2 * b ^ 2 - 6 * a * c) * ((9 * c - a * b) ^ 3 * (9 * c - a * b) ^ 2) +
           c * ((9 * c - a * b) ^ 3 * (9 * c - a * b) ^ 2 * (9 * c - a * b)))
1 * (-a*b + 9*c)^3 * (-a^2*b^2 + 4*a^3*c + 4*b^3 - 18*a*b*c + 27*c^2) * (2*b^3 - 9*a*b*c + 27*c^2)

julia> ((2 * b ^ 2 - 6 * a * c) ^ 3 * (9 * c - a * b) ^ 2 + a * (2 * b ^ 2 - 6 * a * c) ^ 2 * (9 * c - a * b) ^ 3) *
                      (9 * c - a * b) +
                    b * (2 * b ^ 2 - 6 * a * c) * ((9 * c - a * b) ^ 3 * (9 * c - a * b) ^ 2) +
                  c * ((9 * c - a * b) ^ 3 * (9 * c - a * b) ^ 2 * (9 * c - a * b))
2*a^5*b^8 - 17*a^6*b^6*c + 36*a^7*b^4*c^2 - 8*a^3*b^9 + 18*a^4*b^7*c + 324*a^5*b^5*c^2 - 1080*a^6*b^3*c^3 + 216*a^2*b^8*c - 1620*a^3*b^6*c^2 + 243*a^4*b^4*c^3 + 11664*a^5*b^2*c^4 - 1944*a*b^7*c^2 + 20412*a^2*b^5*c^3 - 40824*a^3*b^3*c^4 - 52488*a^4*b*c^5 + 5832*b^6*c^3 - 91854*a*b^4*c^4 + 295245*a^2*b^2*c^5 + 78732*a^3*c^6 + 118098*b^3*c^5 - 708588*a*b*c^6 + 531441*c^7

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a + 3*t - s, 3*t^2 - 2*t*s - b, 3*b*t - b*s + 9*c, 2*b^2 + 18*c*t - 6*c*s, 2*t*s^2, 2*c*s^2, b*s^2 + 3*b^2 + 27*c*t - 9*c*s, t^2*s - b*t - 3*c, b*t*s + b^2 + 9*c*t, t^3 - t^2*s + c, b*t^2 + b^2 + 12*c*t - 2*c*s, b^2*t - b^2*s - 6*c*t*s + 3*b*c)

julia> eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*b^2 - 6*a*c, a*b - 9*c, a^2 - s^2 - 3*b, 2*c*s^2, b*s^2 + b^2 - 3*a*c, 2*a*s^2 - 2*s^3)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*a*t + 3*t^2 + b, 2*b^2 - 6*a*c, a*b - 9*c, t^3 - b*t - 2*c, b*t^2 + b^2 - 2*a*c + 6*c*t, a*t^2 + 3*t^3 - b*t - 3*c, 2*a^2*c - 6*b*c)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*a*t + 3*t^2 + b, 2*b^2 - 6*a*c, a*b - 9*c, t^3 - b*t - 2*c, b*t^2 + b^2 - 2*a*c + 6*c*t, a*t^2 + 3*t^3 - b*t - 3*c, 2*a^2*c - 6*b*c)

julia> R, (a, b, c, x, t, s) = PolynomialRing(QQ, ["a", "b", "c", "x", "t", "s"])
(Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C), spoly{n_Q}[a, b, c, x, t, s])

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (2*a*t + 3*t^2 + b, b^2 - 3*a*c, a*b - 9*c, t^3 - b*t - 2*c, b*t^2 + a*c + 6*c*t, a^2*c - 3*b*c)

julia> eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (b^2 - 3*a*c, a*b - 9*c, a^2 - s^2 - 3*b, c*s^2, b*s^2 + 3*b^2 - 9*a*c, a*s^2 - s^3)

julia>

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, t + s])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, t + s)

julia> eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (c, a - 4*s, 5*s^2 - b, b*s, b^2)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (c, a + 4*t, 5*t^2 - b, b*t, b^2)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (s, a + 3*t, 3*t^2 - b, b*t + 3*c, b^2 + 9*c*t)

julia> R, (a, b, c, x, t, s) = PolynomialRing(ZZ, ["a", "b", "c", "x", "t", "s"])
^[[A^[[A^[[A(Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), spoly{n_Z}[a, b, c, x, t, s])

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, t + s])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, t + s)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (s, a + 3*t, 3*t^2 - b, b*t + 3*c, b^2 + 9*c*t, t^3 + c)

julia> factor( -(a * b * 243) + a ^ 3 * 54 + c * 729)
27 * (2*a^3 - 9*a*b + 27*c)

julia> factor( a * b * 243 + a ^ 3 * 108 + c * 729 )
27 * (4*a^3 + 9*a*b + 27*c)

julia> I = Ideal(R, [(a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), 9 * c - a * b])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, -a*b + 9*c)

julia> st
stacktrace   stat         std_hilbert  stdin        step         strides      strip
startswith   std          stderr       stdout       stride       string       struct
julia> st
stacktrace   stat         std_hilbert  stdin        step         strides      strip
startswith   std          stderr       stdout       stride       string       struct
julia> st
stacktrace   stat         std_hilbert  stdin        step         strides      strip
startswith   std          stderr       stdout       stride       string       struct
julia> std(I)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*b - 9*c, 4*a^3*c + 4*b^3 - 216*c^2, 4*b^4 + 36*a^2*c^2 - 216*b*c^2)

julia> conI
conj                  const                 contains              continue
conj!                 constant_coefficient  content               convert
julia> conI
conj                  const                 contains              continue
conj!                 constant_coefficient  content               convert
julia> contI
contains  content   continue
julia> contains(I,a)
ERROR: MethodError: no method matching contains(::sideal{spoly{n_Z}}, ::spoly{n_Z})
Closest candidates are:
  contains(::AbstractString, ::Any) at strings/util.jl:110
  contains(::sideal{S}, ::sideal{S}) where S at ~/.julia/packages/Singular/zLgw5/src/ideal/ideal.jl:338
  contains(::Any) at strings/util.jl:171
Stacktrace:
 [1] top-level scope
   @ REPL[62]:1

julia> contains
contains (generic function with 30 methods)

julia> lift(I,a)
ERROR: MethodError: no method matching lift(::sideal{spoly{n_Z}}, ::spoly{n_Z})
Closest candidates are:
  lift(::sideal{T}, ::sideal{T}) where T at ~/.julia/packages/Singular/zLgw5/src/ideal/ideal.jl:744
  lift(::sideal{T}, ::sideal{T}, ::Bool, ::Bool, ::Bool) where T at ~/.julia/packages/Singular/zLgw5/src/ideal/ideal.jl:769
Stacktrace:
 [1] top-level scope
   @ REPL[64]:1

julia> lift(a,I)
ERROR: MethodError: no method matching lift(::spoly{n_Z}, ::sideal{spoly{n_Z}})
Closest candidates are:
  lift(::sideal{T}, ::sideal{T}) where T at ~/.julia/packages/Singular/zLgw5/src/ideal/ideal.jl:744
  lift(::sideal{T}, ::sideal{T}, ::Bool, ::Bool, ::Bool) where T at ~/.julia/packages/Singular/zLgw5/src/ideal/ideal.jl:769
Stacktrace:
 [1] top-level scope
   @ REPL[65]:1

julia> lift(Ideal(R,a),I)
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
a^2*b^2-4*a^3*c-4*b^3+18*a*b*c-27*c^2
-a*b+9*c)

julia> lift(Ideal(R,I[0]),I)
ERROR: BoundsError: attempt to access sideal{spoly{n_Z}} at index [0]
Stacktrace:
 [1] checkbounds
   @ ~/.julia/packages/Singular/zLgw5/src/ideal/ideal.jl:46 [inlined]
 [2] getindex(I::sideal{spoly{n_Z}}, i::Int64)
   @ Singular ~/.julia/packages/Singular/zLgw5/src/ideal/ideal.jl:64
 [3] top-level scope
   @ REPL[67]:1

julia> lift(Ideal(R,I[1]),I)
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
a^2*b^2-4*a^3*c-4*b^3+18*a*b*c-27*c^2
-a*b+9*c)

julia> lift(I,Ideal(R,I[1]))
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
gen(1), Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0)

julia> lift(I,Ideal(R,-(a * b * 243) + a ^ 3 * 54 + c * 729))
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
54*a^3-243*a*b+729*c)

julia> lift(I,Ideal(R, a * b * 243 + a ^ 3 * 108 + c * 729))
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
108*a^3+243*a*b+729*c)

julia>

julia> R, (a, b, c, x, t, s) = PolynomialRing(ZZ, ["a", "b", "c", "x", "t", "s"])
(Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), spoly{n_Z}[a, b, c, x, t, s])

julia> R, (a, b, c, x, t, s) = PolynomialRing(QQ, ["a", "b", "c", "x", "t", "s"])
(Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C), spoly{n_Q}[a, b, c, x, t, s])

julia> I = Ideal(R, [(a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), 9 * c - a * b])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, -a*b + 9*c)

julia> lift(I,Ideal(R, a * b * 243 + a ^ 3 * 108 + c * 729))
(Singular Module over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0, Singular Module over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C), with Generators:
108*a^3+243*a*b+729*c)

julia> lift(I,Ideal(R,-(a * b * 243) + a ^ 3 * 54 + c * 729))
(Singular Module over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0, Singular Module over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C), with Generators:
54*a^3-243*a*b+729*c)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s, 6*x + 2*a])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s, 2*a + 6*x)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (s, a + 3*t, 3*t^2 - b, b*t + 3*c, b^2 + 9*c*t)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (s, a + 3*t, 3*t^2 - b, b*t + 3*c, b^2 + 9*c*t)

julia>

julia> R, (a, b, c, x, t, s) = PolynomialRing(ZZ, ["a", "b", "c", "x", "t", "s"])
(Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), spoly{n_Z}[a, b, c, x, t, s])

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (s, a + 3*t, 3*t^2 - b, b*t + 3*c, b^2 + 9*c*t, t^3 + c)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s, 6*x + 2*a])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s, 2*a + 6*x)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (s, a + 3*t, 3*t^2 - b, b*t + 3*c, b^2 + 9*c*t, t^3 + c)

julia> eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (s, b^2 - 3*a*c, a*b - 9*c, a^2 - 3*b)

julia> factor( a * b * 243 + a ^ 3 * 108 + c * 729)
27 * (4*a^3 + 9*a*b + 27*c)

julia> ( a * b * 243 + a ^ 3 * 108 + c * 729) - 27*(a*b - 9*c)
108*a^3 + 216*a*b + 972*c

julia> ( a * b * 243 + a ^ 3 * 108 + c * 729) - 3*27*(a*b - 9*c)
108*a^3 + 162*a*b + 1458*c

julia> ( a * b * 243 + a ^ 3 * 108 + c * 729) + 27*(a*b - 9*c)
108*a^3 + 270*a*b + 486*c

julia> ( a * b * 243 + a ^ 3 * 108 + c * 729) + 3*27*(a*b - 9*c)
108*a^3 + 324*a*b

julia> ( a * b * 243 + a ^ 3 * 108 + c * 729) + 3*27*(a*b - 9*c) - 108*a*(a^2 - 3*b)
648*a*b

julia> -(a * b * 243) + a ^ 3 * 54 + c * 729  + 3*27*(a*b - 9*c) - 108*a*(a^2 - 3*b)
-54*a^3 + 162*a*b

julia> -(a * b * 243) + a ^ 3 * 54 + c * 729  + 3*27*(a*b - 9*c) #- 108*a*(a^2 - 3*b)
54*a^3 - 162*a*b

julia> -(a * b * 243) + a ^ 3 * 54 + c * 729  + 3*27*(a*b - 9*c) +54*a*(a^2 - 3*b)
108*a^3 - 324*a*b

julia> -(a * b * 243) + a ^ 3 * 54 + c * 729  + 3*27*(a*b - 9*c) -54*a*(a^2 - 3*b)
0

julia> I = Ideal(R, [(a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), 9 * c - a * b])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, -a*b + 9*c)

julia> std(I)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*b - 9*c, 4*a^3*c + 4*b^3 - 216*c^2, 4*b^4 + 36*a^2*c^2 - 216*b*c^2)

julia> eliminate(I, c)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (4*a^4*b - 24*a^2*b^2 + 36*b^3)

julia> factor((4*a^4*b - 24*a^2*b^2 + 36*b^3))
4 * (-a^2 + 3*b)^2 * b

julia>

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s, 6*x + 2*a])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s, 2*a + 6*x)

julia> eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (s, b^2 - 3*a*c, a*b - 9*c, a^2 - 3*b)

julia> std(eliminate(eliminate(I, x), t))
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (s, b^2 - 3*a*c, a*b - 9*c, a^2 - 3*b)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (s, a + 3*t, 3*t^2 - b, b*t + 3*c, b^2 + 9*c*t, t^3 + c)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a + 3*t - s, 3*t^2 - 2*t*s - b, 3*b*t - b*s + 9*c, 2*b^2 + 18*c*t - 6*c*s, 2*t*s^2, 2*c*s^2, b*s^2 + 3*b^2 + 27*c*t - 9*c*s, t^2*s - b*t - 3*c, b*t*s + b^2 + 9*c*t, t^3 - t^2*s + c, b*t^2 + b^2 + 12*c*t - 2*c*s, b^2*t - b^2*s - 6*c*t*s + 3*b*c)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*a*t + 3*t^2 + b, 2*b^2 - 6*a*c, a*b - 9*c, t^3 - b*t - 2*c, b*t^2 + b^2 - 2*a*c + 6*c*t, a*t^2 + 3*t^3 - b*t - 3*c, 2*a^2*c - 6*b*c)

julia> eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*b^2 - 6*a*c, a*b - 9*c, a^2 - s^2 - 3*b, 2*c*s^2, b*s^2 + b^2 - 3*a*c, 2*a*s^2 - 2*s^3)

julia> radical(eliminate(eliminate(I, x), s))
ERROR: UndefVarError: radical not defined
Stacktrace:
 [1] top-level scope
   @ REPL[110]:1

julia>

julia> eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*b^2 - 6*a*c, a*b - 9*c, a^2 - s^2 - 3*b, 2*c*s^2, b*s^2 + b^2 - 3*a*c, 2*a*s^2 - 2*s^3)

julia> std(eliminate(eliminate(I, x), s))
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*a*t + 3*t^2 + b, 2*b^2 - 6*a*c, a*b - 9*c, t^3 - b*t - 2*c, b*t^2 + b^2 - 2*a*c + 6*c*t, a*t^2 + 2*b*t + 3*c, 2*a^2*c - 6*b*c)

julia> R, (t,s,a, b, c, x, t, s) = PolynomialRing(ZZ, ["t","s","a", "b", "c", "x"])
ERROR: BoundsError: attempt to access 6-element Vector{spoly{n_Z}} at index [7]
Stacktrace:
 [1] getindex
   @ ./array.jl:924 [inlined]
 [2] indexed_iterate(a::Vector{spoly{n_Z}}, i::Int64, state::Int64)
   @ Base ./tuple.jl:89
 [3] top-level scope
   @ REPL[113]:1

julia> R, (t,s,a, b, c, x,) = PolynomialRing(ZZ, ["t","s","a", "b", "c", "x"])
(Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C), spoly{n_Z}[t, s, a, b, c, x])

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b])
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, 3*t - s + a, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s)])
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, 3*t - s + a, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c)

julia> eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (s^2 - a^2 + 3*b, 2*s*b^2 + a*b^2 - 6*s*a*c - 6*a^2*c + 9*b*c, s*a*b - a^2*b + 6*b^2 - 9*s*c - 9*a*c, 2*s*a^2 - 2*a^3 - 6*s*b + 9*a*b - 27*c, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (3*t^2 + 2*t*a + b, 2*t*b^2 + a*b^2 - 6*t*a*c - 4*a^2*c + 3*b*c, t*a*b + 2*b^2 - 9*t*c - 6*a*c, t^2*b - b^2 + 6*t*c + 4*a*c, 2*t*a^2 - 6*t*b + a*b - 9*c, t^2*a + 2*t*b + 3*c, t^3 - t*b - 2*c, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2)

julia> eliminate(eliminate(I, x), t)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (s^2 - a^2 + 3*b, 2*s*b^2 + a*b^2 - 6*s*a*c - 6*a^2*c + 9*b*c, s*a*b - a^2*b + 6*b^2 - 9*s*c - 9*a*c, 2*s*a^2 - 2*a^3 - 6*s*b + 9*a*b - 27*c, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (3*t^2 + 2*t*a + b, 2*t*b^2 + a*b^2 - 6*t*a*c - 4*a^2*c + 3*b*c, t*a*b + 2*b^2 - 9*t*c - 6*a*c, t^2*b - b^2 + 6*t*c + 4*a*c, 2*t*a^2 - 6*t*b + a*b - 9*c, t^2*a + 2*t*b + 3*c, t^3 - t*b - 2*c, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s, 6*x + 2*a])
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, 3*t - s + a, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s, 2*a + 6*x)

julia>

julia> eliminate(eliminate(eliminate(I, x), s), t)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (b^2 - 3*a*c, a*b - 9*c, a^2 - 3*b)

julia> eliminate(eliminate(eliminate(eliminate(I, x), s), t), c)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (a^2 - 3*b)

julia> eliminate(eliminate(eliminate(I, x), s), t)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (b^2 - 3*a*c, a*b - 9*c, a^2 - 3*b)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, 6*x + 2*a])
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, 2*a + 6*x)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (2*b^2 - 6*a*c, a*b - 9*c, 2*a^2 - 6*b)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s, 6*x + 2*a, a*b - 9*c, 2*a^2 - 6*b])
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, 3*t - s + a, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s, 2*a + 6*x, a*b - 9*c, 2*a^2 - 6*b)

julia> eliminate(I, x)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (s, 3*t + a, b^2 - 3*a*c, a*b - 9*c, t*b + 3*c, a^2 - 3*b, t*a + b, t^3 + c)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, s, a*b - 9*c, 2*a^2 - 6*b])
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, 3*t - s + a, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, s, a*b - 9*c, 2*a^2 - 6*b)

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, a*b - 9*c, 2*a^2 - 6*b])
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, 3*t - s + a, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, a*b - 9*c, 2*a^2 - 6*b)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (2*b^2 - 6*a*c, a*b - 9*c, 2*a^2 - 6*b, 3*t^2 + 2*t*a + b, t^2*b - b^2 + 6*t*c + 4*a*c, t^2*a + 2*t*b + 3*c, t^3 - t*b - 2*c)

julia> std(eliminate(eliminate(I, x), s))
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (2*b^2 - 6*a*c, a*b - 9*c, 2*a^2 - 6*b, 3*t^2 + 2*t*a + b, t^2*b - b^2 + 6*t*c + 4*a*c, t^2*a + 2*t*b + 3*c, t^3 - t*b - 2*c)

julia> eliminate(eliminate(eliminate(I, x), s),t)
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (2*b^2 - 6*a*c, a*b - 9*c, 2*a^2 - 6*b)

julia> std(eliminate(eliminate(I, x), s))
Singular ideal over Singular Polynomial Ring (ZZ),(t,s,a,b,c,x),(dp(6),C) with generators (2*b^2 - 6*a*c, a*b - 9*c, 2*a^2 - 6*b, 3*t^2 + 2*t*a + b, t^2*b - b^2 + 6*t*c + 4*a*c, t^2*a + 2*t*b + 3*c, t^3 - t*b - 2*c)

julia>

julia> R, (a, b, c, x, t, s) = PolynomialRing(ZZ, ["a", "b", "c", "x", "t", "s"])
(Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), spoly{n_Z}[a, b, c, x, t, s])

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, a*b - 9*c, 2*a^2 - 6*b])
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, a*b - 9*c, 2*a^2 - 6*b)

julia> std(eliminate(eliminate(I, x), s))
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*a*t + 3*t^2 + b, 2*b^2 - 6*a*c, a*b - 9*c, 2*a^2 - 6*b, t^3 - b*t - 2*c, b*t^2 + b^2 - 2*a*c + 6*c*t, a*t^2 + 2*b*t + 3*c)

julia> std(eliminate(eliminate(I, x), t))
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*s^2, 2*b^2 - 6*a*c, a*b - 9*c, a^2 - s^2 - 3*b, b*s^2 + b^2 - 3*a*c)

julia> (eliminate(eliminate(I, x), t))
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*s^2, 2*b^2 - 6*a*c, a*b - 9*c, a^2 - s^2 - 3*b, b*s^2 + b^2 - 3*a*c)

julia> lift(Ideal(R, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2),Ideal(R,9 * c - a * b))
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
-a*b+9*c)

julia> lift(Ideal(R, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2),Ideal(R,[9 * c - a * b,2 * (a ^ 2 - 3 * b)]))
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
-a*b+9*c
2*a^2-6*b)

julia> lift(Ideal(R, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2),Ideal(R,[9 * c - a * b,2 * (a ^ 2 - 3 * b),2 * (b ^ 2 - 3 * a * c)]))
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
-a*b+9*c
2*a^2-6*b
2*b^2-6*a*c)

julia> lift(Ideal(R, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2),Ideal(R,[9 * c - a * b,2 * (a ^ 2 - 3 * b),(b ^ 2 - 3 * a * c)]))
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
-a*b+9*c
2*a^2-6*b
b^2-3*a*c)

julia> lift(Ideal(R, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2),Ideal(R,[9 * c - a * b,(a ^ 2 - 3 * b),(b ^ 2 - 3 * a * c)]))
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
-a*b+9*c
a^2-3*b
b^2-3*a*c)

julia> lift(Ideal(R, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2),Ideal(R,[9 * c - a * b,(a ^ 2 - 3 * b),(b ^ 2 - 3 * a * c)]))
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
-a*b+9*c
a^2-3*b
b^2-3*a*c)

help?> radical
search: AbstractDict CartesianIndices

Couldn't find radical
Perhaps you meant rad2deg
  No documentation found.

  Binding radical does not exist.

help?> root
search: promote promote_type promote_rule promote_shape errormonitor InsertionSort ResolutionSet apropos RoundDown RoundToZero AlgebraHomomorphism

Couldn't find root
Perhaps you meant sort, acot, cot, Bool, promote, round, nrows, kron, kron!, prod, prod!, error, rank, rand, read, real, reim, rem, repr, reset or rm
  No documentation found.

  Binding root does not exist.

julia> root(I)
ERROR: UndefVarError: root not defined
Stacktrace:
 [1] top-level scope
   @ REPL[147]:1

julia>

julia> I
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, a*b - 9*c, 2*a^2 - 6*b)

julia> lift(Ideal(R, 2 * (b ^ 2 - 3 * a * c)), I)
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0
0
0
0
0
0
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
a*x^2+x^3+b*x+c
2*a*x+3*x^2+b
a^2*b^2-4*a^3*c-4*b^3+18*a*b*c-27*c^2
a+3*t-s
-3*t^2+2*t*s+b
t^3-t^2*s+c
-a*b+9*c
a*b-9*c
2*a^2-6*b)

julia> lift(Ideal(R, 2 * (b ^ 2 - 3 * a * c))^2, I)
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0
0
0
0
0
0
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
a*x^2+x^3+b*x+c
2*a*x+3*x^2+b
a^2*b^2-4*a^3*c-4*b^3+18*a*b*c-27*c^2
a+3*t-s
-3*t^2+2*t*s+b
t^3-t^2*s+c
-a*b+9*c
a*b-9*c
2*a^2-6*b)

julia> lift(Ideal(R, 2 * (b ^ 2 - 3 * a * c))^3, I)
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0
0
0
0
0
0
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
a*x^2+x^3+b*x+c
2*a*x+3*x^2+b
a^2*b^2-4*a^3*c-4*b^3+18*a*b*c-27*c^2
a+3*t-s
-3*t^2+2*t*s+b
t^3-t^2*s+c
-a*b+9*c
a*b-9*c
2*a^2-6*b)

julia> lift(Ideal(R, 2 * (b ^ 2 - 3 * a * c))^6, I)
(Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
0
0
0
0
0
0
0
0
0, Singular Module over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C), with Generators:
a*x^2+x^3+b*x+c
2*a*x+3*x^2+b
a^2*b^2-4*a^3*c-4*b^3+18*a*b*c-27*c^2
a+3*t-s
-3*t^2+2*t*s+b
t^3-t^2*s+c
-a*b+9*c
a*b-9*c
2*a^2-6*b)

julia> eliminate(eliminate(eliminate(I, x), s),t)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*b^2 - 6*a*c, a*b - 9*c, 2*a^2 - 6*b)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (ZZ),(a,b,c,x,t,s),(dp(6),C) with generators (2*a*t + 3*t^2 + b, 2*b^2 - 6*a*c, a*b - 9*c, 2*a^2 - 6*b, t^3 - b*t - 2*c, b*t^2 + b^2 - 2*a*c + 6*c*t, a*t^2 + 15*t^3 - 13*b*t - 27*c)

julia> R, (a, b, c, x, t, s) = PolynomialRing(QQ, ["a", "b", "c", "x", "t", "s"])
(Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C), spoly{n_Q}[a, b, c, x, t, s])

julia> I = Ideal(R, [x^3 + a * x ^2 + b*x + c, 3*x^2 + 2*a *x + b, (a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2), a + 3*t - s, b - (3*t^2 - 2*t*s), c - (-t^3 + t^2 * s), 9 * c - a * b, a*b - 9*c, 2*a^2 - 6*b])
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (a*x^2 + x^3 + b*x + c, 2*a*x + 3*x^2 + b, a^2*b^2 - 4*a^3*c - 4*b^3 + 18*a*b*c - 27*c^2, a + 3*t - s, -3*t^2 + 2*t*s + b, t^3 - t^2*s + c, -a*b + 9*c, a*b - 9*c, 2*a^2 - 6*b)

julia> eliminate(eliminate(I, x), s)
Singular ideal over Singular Polynomial Ring (QQ),(a,b,c,x,t,s),(dp(6),C) with generators (2*a*t + 3*t^2 + b, b^2 - 3*a*c, a*b - 9*c, a^2 - 3*b, t^3 - b*t - 2*c, b*t^2 + a*c + 6*c*t)


-/
