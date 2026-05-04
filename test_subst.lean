import FOL.FOL

mutual
theorem liftTerm_comm (b a : Nat) (h : b ≤ a) (t : Term) :
    liftTerm (a + 1) (liftTerm b t) = liftTerm b (liftTerm a t) := by
  match t with
  | .bvar n =>
    by_cases h1 : n < b
    · have h2 : n < a := by omega
      have h3 : n < a + 1 := by omega
      simp [liftTerm, h1, h2, h3]
    · by_cases h2 : n < a
      · have h3 : n < a + 1 := by omega
        have h4 : ¬(n + 1 < b) := by omega
        simp [liftTerm, h1, h2, h3, h4]
      · by_cases h3 : n < a + 1
        · have h4 : ¬(n + 1 < b) := by omega
          simp [liftTerm, h1, h2, h3, h4]; try omega
        · have h4 : ¬(n + 1 < b) := by omega
          simp [liftTerm, h1, h2, h3, h4]; try omega
  | .fvar _ => rfl
  | .func f ts =>
    simp only [liftTerm]
    exact congrArg (Term.func f) (liftTerms_comm b a h ts)

theorem liftTerms_comm (b a : Nat) (h : b ≤ a) (ts : List Term) :
    liftTerms (a + 1) (liftTerms b ts) = liftTerms b (liftTerms a ts) := by
  match ts with
  | []       => rfl
  | t :: ts' =>
    simp only [liftTerms]
    have ht := liftTerm_comm b a h t
    have hts := liftTerms_comm b a h ts'
    rw [ht, hts]
end
