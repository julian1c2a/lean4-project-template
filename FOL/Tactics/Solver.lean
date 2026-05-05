import FOL.FOL
import FOL.Tactics.Basic
open Lean Meta Elab Tactic

elab "prove_mem" : tactic => do
  let goal ← getMainGoal
  tryMem goal
  setGoals []
