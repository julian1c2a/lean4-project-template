import FOL.FOL
namespace FOL.Metamath.Semantics

structure Model (D : Type) where
  func : String → List D → D
  rel  : String → List D → Prop

mutual
def evalTerm {D : Type} (M : Model D) (v : Nat → D) (t : Term) : D :=
  match t with
  | .bvar n => v n
  | .func f ts => M.func f (evalTerms M v ts)

def evalTerms {D : Type} (M : Model D) (v : Nat → D) (ts : List Term) : List D :=
  match ts with
  | [] => []
  | t :: ts' => evalTerm M v t :: evalTerms M v ts'
end

def updateEnv {D : Type} (c : Nat) (v : Nat → D) (d : D) : Nat → D :=
  fun n =>
    if n < c then v n
    else if n = c then d
    else v (n - 1)

mutual
theorem eval_liftTerm_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (t : Term) :
    evalTerm M (updateEnv c v d) (liftTerm c t) = evalTerm M v t := by
  match t with
  | .bvar n =>
    by_cases h : n < c
    · simp [liftTerm, evalTerm, updateEnv, h]
    · have h1 : ¬(n + 1 < c) := by omega
      have h2 : ¬(n + 1 = c) := by omega
      have h3 : n + 1 - 1 = n := by omega
      simp [liftTerm, evalTerm, updateEnv, h, h1, h2, h3]
  | .func f ts =>
    have ih := eval_liftTerms_ext M v d c ts
    simp [liftTerm, evalTerm, ih]

theorem eval_liftTerms_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (ts : List Term) :
    evalTerms M (updateEnv c v d) (liftTerms c ts) = evalTerms M v ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    have ih1 := eval_liftTerm_ext M v d c t
    have ih2 := eval_liftTerms_ext M v d c ts'
    simp [liftTerms, evalTerms, ih1, ih2]
end

mutual
theorem eval_substTerm_ext {D : Type} (M : Model D) (v : Nat → D) (s : Term) (c : Nat) (t : Term) :
    evalTerm M v (substTerm c s t) = evalTerm M (updateEnv c v (evalTerm M v s)) t := by
  match t with
  | .bvar n =>
    by_cases h1 : n = c
    · have h2 : ¬(n < c) := by omega
      simp [substTerm, evalTerm, updateEnv, h1, h2]
    · by_cases h3 : n < c
      · have h4 : ¬(n > c) := by omega
        simp [substTerm, evalTerm, updateEnv, h1, h3, h4]
      · have h4 : n > c := by omega
        simp [substTerm, evalTerm, updateEnv, h1, h3, h4]
  | .func f ts =>
    have ih := eval_substTerms_ext M v s c ts
    simp [substTerm, evalTerm, ih]

theorem eval_substTerms_ext {D : Type} (M : Model D) (v : Nat → D) (s : Term) (c : Nat) (ts : List Term) :
    evalTerms M v (substTerms c s ts) = evalTerms M (updateEnv c v (evalTerm M v s)) ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    have ih1 := eval_substTerm_ext M v s c t
    have ih2 := eval_substTerms_ext M v s c ts'
    simp [substTerms, evalTerms, ih1, ih2]
end

end FOL.Metamath.Semantics