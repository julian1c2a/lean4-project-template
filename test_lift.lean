import FOL.FOL

theorem liftTerm_comm (b a : Nat) (h : b ≤ a) (t : Term) :
    liftTerm (a + 1) (liftTerm b t) = liftTerm b (liftTerm a t) := by
  match t with
  | .bvar n =>
    simp only [liftTerm]
    split_ifs
    sorry
  | .fvar _ => rfl
  | .func f ts => sorry