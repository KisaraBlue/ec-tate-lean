import Mathlib.Tactic.Basic

-- TODO do we need more types as implied by https://mathoverflow.net/questions/127908/reduction-types-of-elliptic-curves

inductive Kodaira where
  | I     : Nat → Kodaira --for both I0 and In with n > 0
  | II    : Kodaira
  | III   : Kodaira
  | IV    : Kodaira
  | Is    : Nat → Kodaira -- TODO really Is 0 shouldn't occur?
  | IIs   : Kodaira
  | IIIs  : Kodaira
  | IVs   : Kodaira
deriving DecidableEq, Inhabited

open Kodaira

instance : Repr Kodaira where
  reprPrec
    | I m, _   => "I" ++ repr m
    | II, _    => "II"
    | III, _   => "III"
    | IV, _    => "IV"
    | Is m, _  => "I*" ++ repr m
    | IIs, _   => "II*"
    | IIIs, _  => "III*"
    | IVs, _   => "IV*"

lemma eq_I_Nat (m n : Nat) : m = n ↔ I m = I n := by
  apply Iff.intro
  intro h
  exact congrArg I h
  intro h
  cases h
  rfl

lemma eq_Is_Nat (m n : Nat) : m = n ↔ Is m = Is n := by
  apply Iff.intro
  intro h
  exact congrArg Is h
  intro h
  cases h
  rfl

inductive ReductionType
  | Good
  | SplitMultiplicative
  | NonSplitMultiplicative
  | Additive
deriving DecidableEq, Repr, Inhabited

def ReductionType.to_lmfdb : ReductionType → Int
  | Good                   => unreachable! -- LMFDB has no code for good reduction
  | SplitMultiplicative    => 1
  | NonSplitMultiplicative => -1
  | Additive               => 0
