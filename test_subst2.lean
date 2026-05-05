import FOL.FOL

mutual
theorem fvarSubst_subst_term (c : String) (s : Term) (t : Term)
    (hfree : fvarFreeTerm c t = true) :
    fvarSubstTerm c s (substTerm 0 (Term.fvar c) t) = substTerm 0 s t := by
  match t with
  | .bvar n =>
    simp only [substTerm]
    split
    · simp [fvarSubstTerm]
    · split
      · simp only [fvarSubstTerm]
      · simp only [fvarSubstTerm]
  | .fvar x =>
    simp only [fvarFreeTerm, Bool.not_eq_true', decide_eq_false_iff_not] at hfree
    simp only [substTerm, fvarSubstTerm]
    split
    · exact absurd (by assumption) hfree
    · simp [fvarSubstTerm, by assumption]
  | .func f ts =>
    simp only [substTerm, fvarSubstTerm]
    exact congrArg (Term.func f) (fvarSubst_subst_terms c s ts hfree)

theorem fvarSubst_subst_terms (c : String) (s : Term) (ts : List Term)
    (hfree : fvarFreeTerms c ts = true) :
    fvarSubstTerms c s (substTerms 0 (Term.fvar c) ts) = substTerms 0 s ts := by
  match ts with
  | []       => rfl
  | t :: ts' =>
    simp only [fvarFreeTerms, Bool.and_eq_true] at hfree
    simp only [substTerms, fvarSubstTerms]
    have ht := fvarSubst_subst_term c s t hfree.1
    have hts := fvarSubst_subst_terms c s ts' hfree.2
    rw [ht, hts]
end
