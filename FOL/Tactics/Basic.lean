import FOL.FOL
import Lean
open Lean Meta Elab Tactic

partial def getAllPositions (f : Formula) : List Pos :=
  match f with
  | .impl f1 f2 => .root :: (getAllPositions f1).map .left ++ (getAllPositions f2).map .right
  | .and f1 f2 => .root :: (getAllPositions f1).map .left ++ (getAllPositions f2).map .right
  | .or f1 f2 => .root :: (getAllPositions f1).map .left ++ (getAllPositions f2).map .right
  | .forall f1 => .root :: (getAllPositions f1).map .body
  | .ex f1 => .root :: (getAllPositions f1).map .body
  | _ => [.root]

-- A tactic to close the goal `Γ ⊢ f` if `f ∈ Γ`.
partial def tryMem (g : MVarId) : MetaM Unit := do
  try
    let _ ← g.apply (← mkConstWithFreshMVarLevels ``List.Mem.head)
    pure ()
  catch _ =>
    let newGoals ← g.apply (← mkConstWithFreshMVarLevels ``List.Mem.tail)
    if h : newGoals.length = 1 then
      tryMem newGoals[0]
    else
      throwError "prove_mem failed"

elab "derive_hyp" : tactic => do
  evalTactic (← `(tactic| apply Derives.hyp))
  let goal ← getMainGoal
  tryMem goal
  setGoals []

-- Tactic to automate rewrite_at
-- It tries to close the goal `Γ ⊢ f'` by finding `f ∈ Γ`, a position `p`, and a `LocalRule`
-- such that `f` rewrites to `f'`.

syntax "derive_rewrite " term " at " term : tactic

macro_rules
  | `(tactic| derive_rewrite $rule at $pos) => `(tactic| apply Derives.rewrite_at $pos <;> exact $rule)

-- Tactic to automate weakening
-- Automatically applies `Derives.weakening` and tries to close the subset goal
syntax "derive_weaken " term : tactic

macro_rules
  | `(tactic| derive_weaken $thm) => `(tactic| apply Derives.weakening $thm; repeat (apply List.subset_cons <|> exact List.Subset.refl _))

-- Tactic to automate Reductio ad Absurdum (RAA)
syntax "derive_raa" : tactic

macro_rules
  | `(tactic| derive_raa) => `(tactic| apply Derives.raa)

-- Tactic to automate Reflexivity of Equality
syntax "derive_refl" : tactic

macro_rules
  | `(tactic| derive_refl) => `(tactic| apply Derives.eq_refl)
