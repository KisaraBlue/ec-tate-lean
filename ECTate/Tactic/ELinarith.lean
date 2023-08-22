import Mathlib.Tactic.Linarith
import ECTate.Data.Nat.Enat
import ECTate.Tactic.SimpSafe
open Qq Lean Meta Tactic Mathlib.Tactic.Ring


-- TODO double check for upstream changes
-- TODO make it less enat specific
-- TODO would be better to make it work bottom up
def is_enat_atom (e : Expr) : Mathlib.Tactic.AtomM (Bool × Bool) :=
  fun rctx ↦ do
    try
      let e ← withReducible <| whnf e
      let ⟨.zero, α, e⟩ ← inferTypeQ' e | failure
      guard (α == q(ENat))
      let sα ← synthInstanceQ (q(CommSemiring $α) : Q(Type 0)) -- TODO this will be enat every time.
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
-- example : (⊤ : ℕ∞) * 2 = a := by simp? -- TODO why does this not return top_add?? is decide taking precedence
-- example : (⊤ : ℕ∞) + 1 = ⊤ := by simp? -- TODO why does this not return top_add?? is decide taking precedence
-- example : (⊤ : ℕ∞) + 1 = a := by simp
-- example : (⊤ : ℕ∞) + (0: ℕ) = a := by simp [-CharP.cast_eq_zero, add_zero]
-- example : (1 : ZMod 3) + (0: ℕ) = a := by simp only [Nat.cast_zero, add_zero]
-- example : (a : ℕ∞) ≤ ⊤ := by
--   simp?
-- example : (a : ℕ∞) + (0: ℕ) = a := by
--   cases a

--


#check Nat.cast_add
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
            let b ← is_enat_atom e'
            if b.1 then
              set ((← get).push e')
            pure ¬ (b.1 ∨ b.2)
      #[]
  -- logInfo (← getMainGoal)
  let mut goals := [← getMainGoal]
  for e in a do
    let id := mkIdent <| Name.str .anonymous (toString <| ← delab e)
    let tac ←
      `(tactic| cases $id : ($(← Expr.toSyntax e):term : ENat) <;>
                -- trace_state <;>
                -- how to check these lemmas exist at compile time?
                simp_safe (config := {failIfUnchanged := false, zeta := false}) only [$id:ident, --ENat.ofN_eq_ofNat,
                  top_add, add_top,
                  ENat.infty_mul, ENat.mul_infty, ite_true, ite_false,
                  Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
                  Nat.cast_zero, Nat.zero_eq, Nat.mul_zero, Nat.zero_le,
                  le_top, top_le_iff, ENat.lt_top
                ] at * <;>
                -- trace_state <;>
                norm_cast at * <;>
                -- trace_state <;>
                try linarith) -- TODO move after everything
    -- logInfo e
    let mut newgs := []
    for g in goals do
      let o ← Elab.runTactic g tac
      newgs := newgs ++ o.1
    goals := newgs
  appendGoals goals


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
