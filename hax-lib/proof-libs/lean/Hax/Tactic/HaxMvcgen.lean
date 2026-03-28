import Hax.Tactic.SpecSet
import Hax.Tactic.Init

namespace Hax.HaxMvcgen

open Lean Elab Syntax Parser Tactic Meta

def mkMvcgenCall (args: Array Name) (cfgStx : Syntax) (argStx : Syntax) : CoreM Syntax := do
  let cfgStx : TSyntax `Lean.Parser.Tactic.optConfig := .mk cfgStx
  let mut elems := argStx[1].getArgs.getSepElems
  for arg in args do
    elems := elems.push
      (Syntax.node .none ``Lean.Parser.Tactic.simpLemma #[mkNullNode, mkNullNode, mkIdent arg])
  let argStx : TSepArray _ _ := Syntax.TSepArray.ofElems (elems.map .mk)
  let tac := ← `(tactic| mvcgen $cfgStx [$argStx,*])
  pure tac

/-- Check if a goal's type is a Triple (i.e., `⦃P⦄ f ⦃Q⦄`). -/
def isTripleGoal (goal : MVarId) : MetaM Bool := do
  let ty ← goal.getType
  return ty.isAppOf `Std.Do.Triple

/-- Find the first Triple hypothesis in the local context of a goal.
Returns the `FVarId` of the hypothesis if found. -/
def findTripleHyp (goal : MVarId) : MetaM (Option FVarId) := do
  goal.withContext do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isAuxDecl then continue
      if decl.type.isAppOf `Std.Do.Triple then
        return some decl.fvarId
    return none

/-- Apply `Triple.of_hypothesis` to a goal using a Triple hypothesis.
Returns the new goals (with the `h` subgoal closed). -/
def applyTripleOfHypothesis (goal : MVarId) (tripleHyp : FVarId) :
    TacticM (Array MVarId) := do
  -- Apply Triple.of_hypothesis, which produces subgoals for `h` and `hp`
  let newGoals ← goal.apply (mkConst `Triple.of_hypothesis)
  -- Find and close the `h` subgoal (the one matching our hypothesis)
  let mut remainingGoals := #[]
  for g in newGoals do
    let closed ← observing? do
      g.withContext do
        let hyp := mkFVar tripleHyp
        let hypType ← inferType hyp
        let goalType ← g.getType
        if (← isDefEq hypType goalType) then
          g.assign hyp
        else
          throwError "type mismatch"
    if closed.isSome then
      continue
    else
      -- Clear the Triple hypothesis from remaining goals to prevent infinite loops
      match ← observing? (g.clear tripleHyp) with
      | some g' => remainingGoals := remainingGoals.push g'
      | none => remainingGoals := remainingGoals.push g
  return remainingGoals

/-- Process goals after mvcgen: find Triple hypotheses and apply `Triple.of_hypothesis`.
Returns `(newTripleGoals, otherGoals, changed)`. -/
def processTripleHypotheses (goals : List MVarId) :
    TacticM (List MVarId × List MVarId × Bool) := do
  let mut newTripleGoals : List MVarId := []
  let mut otherGoals : List MVarId := []
  let mut changed := false
  for goal in goals do
    if ← goal.isAssigned then continue
    if ← isTripleGoal goal then
      -- Goal is itself a Triple — feed it to mvcgen in the next iteration
      newTripleGoals := newTripleGoals ++ [goal]
      changed := true
    else
      match ← findTripleHyp goal with
      | some fvarId =>
        -- Apply Triple.of_hypothesis
        let newGoals ← applyTripleOfHypothesis goal fvarId
        -- The remaining goals from apply should include the `hp` Triple goal
        for g in newGoals do
          if ← isTripleGoal g then
            newTripleGoals := newTripleGoals ++ [g]
          else
            otherGoals := otherGoals ++ [g]
        changed := true
      | none =>
        otherGoals := otherGoals ++ [goal]
  return (newTripleGoals, otherGoals, changed)

syntax (name := hax_mvcgen) "hax_mvcgen" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? : tactic

/-- A customized version of the `mvcgen` tactic. It provides `mvcgen` with additional lemmas
gathered from `@[specset X]` annotations, where `X` is the current setting of
`set_option hax_mvcgen.specset`.

Additionally, after each `mvcgen` run, it scans remaining goals for Triple hypotheses
(from spec lemmas with Triples in pre/postconditions) and applies `Triple.of_hypothesis`
to convert them into new Triple goals, which are then processed by another `mvcgen` run.
This loop continues until no more Triple hypotheses or Triple goals are found.

**Known limitation**: The `Triple.of_hypothesis` lemma must not be visible to `mvcgen`'s
spec resolution, as `mvcgen` will pick it up as a spec and loop infinitely. The hypothesis
handling is currently disabled pending a fix (either constructing the proof term
programmatically or hiding the lemma from `mvcgen`). The Triple-as-goal case (from
preconditions containing Triples) works correctly. -/
@[tactic hax_mvcgen]
def elabHaxMvcgen : Tactic := fun stx => do
  let specset := hax_mvcgen.specset.get (← getOptions)
  let cfgStx := stx[1]
  let argStx := stx[2]
  let extState := specSetExt.getState (← getEnv)
  let decls := (extState.getD specset.toName {}).toArray
  let tac ← mkMvcgenCall decls cfgStx argStx
  -- Initial mvcgen run on all goals
  Tactic.evalTactic tac
  -- Loop: process Triple goals/hypotheses and re-run mvcgen on new Triple goals
  repeat do
    let allGoals ← getGoals
    let (newTripleGoals, otherGoals, changed) ← processTripleHypotheses allGoals
    unless changed do break
    -- Run mvcgen only on the new Triple goals
    setGoals newTripleGoals
    Tactic.evalTactic tac
    -- Restore all goals: mvcgen results + other goals from before
    let mvcgenResults ← getGoals
    setGoals (mvcgenResults ++ otherGoals)

end  Hax.HaxMvcgen
