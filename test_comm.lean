import FOL.Semantics.Basic

theorem shiftEnv_updateEnv_comm2 {D : Type} (v : Nat → D) (c : Nat) (d d' : D) :
    shiftEnv (updateEnv c v d) d' = updateEnv (c + 1) (shiftEnv v d') d := by
  funext n
  cases n with
  | zero => rfl
  | succ n' =>
    dsimp [shiftEnv, updateEnv]
    split
    · rename_i h
      have h1 : n' + 1 < c + 1 := by omega
      simp [h1]
    · rename_i h
      split
      · rename_i h2
        have h3 : ¬(n' + 1 < c + 1) := by omega
        have h4 : n' + 1 = c + 1 := by omega
        simp [h3, h4]
      · rename_i h2
        have h3 : ¬(n' + 1 < c + 1) := by omega
        have h4 : ¬(n' + 1 = c + 1) := by omega
        simp [h3, h4]
