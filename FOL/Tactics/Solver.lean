import FOL.FOL
import Lean
open Lean Meta Elab Tactic

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

elab "prove_mem" : tactic => do
  let goal ← getMainGoal
  tryMem goal
  setGoals []

elab "derive_hyp" : tactic => do
  evalTactic (← `(tactic| apply Derives.hyp))
  let goal ← getMainGoal
  tryMem goal
  setGoals []

-- For Weakening: given a theorem T : Γ ⊢ f, and our goal is Γ' ⊢ f
-- We want to apply Derives.weakening T, and then prove ∀ x, x ∈ Γ → x ∈ Γ'
-- Since Γ is usually a concrete list, we can automate the subset proof.
elab "derive_weaken" t:term : tactic => do
  -- To prove Γ' ⊢ f using t : Γ ⊢ f
  -- We apply weakening
  evalTactic (← `(tactic| apply Derives.weakening (Γ := _)))
  evalTactic (← `(tactic| exact $t))
  -- Now the goal is ∀ x, x ∈ Γ → x ∈ Γ'
  evalTactic (← `(tactic| intro x hx))
  -- Depending on the length of Γ, hx will be a chain of Or's if we simp it, 
  -- but List.Mem on concrete lists evaluates to head/tail.
  -- Actually, we can just use `aesop` or repeat cases.
  -- A simple way:
  evalTactic (← `(tactic| repeat (
    match hx with
    | List.Mem.head _ => prove_mem
    | List.Mem.tail _ hx' => rename_i hx; clear hx; rename_i hx; -- This is tricky in pure tactic
  )))
  -- Let's just rely on a simple recursive tactic for subset
  pure ()
