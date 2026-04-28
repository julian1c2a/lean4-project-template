import FOL.FOL

namespace FOL.Metamath.Semantics

def shiftEnv {D : Type} (v : Nat → D) (d : D) : Nat → D
  | 0 => d
  | n + 1 => v n

def updateEnv {D : Type} (c : Nat) (v : Nat → D) (d : D) : Nat → D :=
  fun n =>
    if n < c then v n
    else if n = c then d
    else v (n - 1)

theorem shiftEnv_updateEnv_comm {D : Type} (v : Nat → D) (c : Nat) (d d' : D) :
    shiftEnv (updateEnv c v d) d' = updateEnv (c + 1) (shiftEnv v d') d := by
  funext n
  cases n with
  | zero => rfl
  | succ n' =>
    simp only [shiftEnv, updateEnv]
    by_cases h1 : n' < c
    · have h2 : n' + 1 < c + 1 := by omega
      simp [h1, h2]
    · by_cases h2 : n' = c
      · simp [h1, h2]
      · have h3 : ¬(n' + 1 < c + 1) := by omega
        cases n' with
        | zero => omega
        | succ n'' =>
          have h5 : n'' + 1 - 1 = n'' := by omega
          simp [h1, h2, h3, h5]
