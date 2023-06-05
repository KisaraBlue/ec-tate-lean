import Mathlib.Tactic.Linarith
import ECTate.Data.Nat.Enat
import ECTate.Tactic.SimpSafe
open Qq Lean Meta Tactic Mathlib.Tactic.Ring

def is_atom (e : Expr) : Mathlib.Tactic.AtomM (Bool × Bool) :=
  fun rctx ↦ do
    try
      let e ← withReducible <| whnf e
      let ⟨.succ u, α, e⟩ ← inferTypeQ e | failure
      let sα ← synthInstanceQ (q(CommSemiring $α) : Q(Type u))
      let c ← mkCache sα
      match ← isAtomOrDerivable sα c e rctx with
      | some none => pure (.true, .false)
      | some (some _) => pure (.false, .true)
      | _ => pure (.false, .false)
    catch _ => pure (.false, .false)


-- /-- Run a computation in the `AtomM` monad and return the atoms. -/
-- def Mathlib.Tactic.AtomM.run' (red : TransparencyMode) (m : AtomM α)
--     (evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }) :
--     MetaM (α × AtomM.State)  :=
--   (m { red, evalAtom }).run {}

open Lean Meta Elab Tactic Term PrettyPrinter in
elab "elinarith" : tactic => do
  let mvarId ← getMainTarget
  -- logInfo mvarId
  -- (←getMainGoal).withContext do
  --   withLocalDeclDQ (← mkFreshUserName `x) q(ℤ) fun x => do
  --   let e : Q(Prop) := q($x ≤ $x+2)
  -- let e : Q(Prop) := mvarId --q($x ≤ $x+2)
  -- get all atoms using ring
  let (_, a) ← Mathlib.Tactic.AtomM.run .default do
    StateT.run (σ := Array Expr) do
        mvarId.forEach' fun e' =>
          do
            let b ← is_atom e'
            if b.1 then
              set ((← get).push e')
            pure ¬ (b.1 ∨ b.2)
      #[]
  -- logInfo (← getMainGoal)
  let mut goals := [← getMainGoal]
  for e in a do
    let tac ←
      `(tactic| cases h : ($(←delab e):term : Enat) <;>
                -- trace_state <;>
                simp_safe only [h, Enat.ofN_eq_ofNat, Enat.top_add, Enat.add_top,
                  Enat.ofNatAtLeastTwoMulInfty, Enat.inftyMulofNatAtLeastTwo,
                  Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
                  Nat.cast_zero, Nat.zero_eq, Nat.mul_zero, Nat.zero_le,
                  Enat.le_top, Enat.lt_top
                ] at * <;>
                -- trace_state <;>
                norm_cast at * <;>
                -- trace_state <;>
                try linarith) -- TODO move after
    -- logInfo e
    let mut newgs := []
    for g in goals do
      let o ← Elab.runTactic g tac
      newgs := newgs ++ o.1
    goals := newgs
  appendGoals goals
-- TODO spell check all comments / docstrings
-- TODO minimiser
-- TODO go to definition in doc comments eg `Mathlib.Tactic.casesMatching`

-- #check Mathlib.Tactic.casesMatching



/-

many tactics work like:

some defined language of functions normally coming from a TC
reified into a language
do something


issues with this is sensitive to language
good to have some boilerplate so we
unfolds unrecognised functions
e.g. group tactic should be ok with `[g, h]` because the definition of `[g,h]` is ghginv hinv.
-/
