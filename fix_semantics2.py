import re

with open('FOL/Semantics.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Fix evalFormula
content = content.replace(
    "| .bottom => False\n  | .atom p ts => M.rel p (evalTerms M v ts)",
    "| .bottom => False\n  | .eq t1 t2 => evalTerm M v t1 = evalTerm M v t2\n  | .atom p ts => M.rel p (evalTerms M v ts)"
)

# Fix evalFormula reserved words
content = content.replace("| .forall f1 =>", "| .«forall» f1 =>")
content = content.replace("| .ex f1 =>", "| .«ex» f1 =>")
content = content.replace("| forall f1 ih =>", "| «forall» f1 ih =>")
content = content.replace("| ex f1 ih =>", "| «ex» f1 ih =>")


# Fix eval_liftTerm_ext
lift_old = """  | .var n =>
    unfold liftTerm evalTerm updateEnv
    split
    · rename_i h
      simp [h]
    · rename_i h
      have h1 : ¬(n + 1 < c) := by omega
      have h2 : ¬(n + 1 = c) := by omega
      have h3 : n + 1 - 1 = n := by omega
      simp [h, h1, h2, h3]
  | .func f ts =>
    unfold liftTerm evalTerm
    have ih := eval_liftTerms_ext M v d c ts
    rw [ih]

theorem eval_liftTerms_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (ts : List Term) :
    evalTerms M (updateEnv c v d) (liftTerms c ts) = evalTerms M v ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    unfold liftTerms evalTerms
    have ih1 := eval_liftTerm_ext M v d c t
    have ih2 := eval_liftTerms_ext M v d c ts'
    rw [ih1, ih2]"""

lift_new = """  | .var n =>
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
    simp [liftTerms, evalTerms, ih1, ih2]"""
content = content.replace(lift_old, lift_new)


# Fix eval_substTerm_ext
subst_old = """  | .var n =>
    unfold substTerm evalTerm updateEnv
    split
    · rename_i h
      have h1 : ¬(n < c) := by omega
      simp [h, h1]
    · rename_i h
      split
      · rename_i h2
        have h3 : ¬(n < c) := by omega
        have h4 : ¬(n = c) := by omega
        simp [h3, h4]
      · rename_i h2
        have h3 : n < c := by omega
        simp [h3]
  | .func f ts =>
    unfold substTerm evalTerm
    have ih := eval_substTerms_ext M v s c ts
    rw [ih]

theorem eval_substTerms_ext {D : Type} (M : Model D) (v : Nat → D) (s : Term) (c : Nat) (ts : List Term) :
    evalTerms M v (substTerms c s ts) = evalTerms M (updateEnv c v (evalTerm M v s)) ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    unfold substTerms evalTerms
    have ih1 := eval_substTerm_ext M v s c t
    have ih2 := eval_substTerms_ext M v s c ts'
    rw [ih1, ih2]"""

subst_new = """  | .var n =>
    by_cases h1 : n = c
    · have h2 : ¬(n < c) := by omega
      simp [substTerm, evalTerm, updateEnv, h1]
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
    simp [substTerms, evalTerms, ih1, ih2]"""
content = content.replace(subst_old, subst_new)

cases_old = """    cases f <;> simp only [getAt?, replaceAt, evalFormula] at hGet ⊢ <;> try contradiction
    · have h := ih hGet v; tauto
    · have h := ih hGet v; tauto
    · have h := ih hGet v; tauto"""

cases_new = """    cases f <;> simp only [getAt?, replaceAt, evalFormula] at hGet ⊢ <;> try contradiction <;> { have h := ih hGet v; tauto }"""

content = content.replace(cases_old, cases_new)

with open('FOL/Semantics.lean', 'w', encoding='utf-8') as f:
    f.write(content)
