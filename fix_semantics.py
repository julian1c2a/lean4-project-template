import re

with open('FOL/Semantics.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Fix evalFormula
content = content.replace(
    "| .bottom => False\n  | .atom p ts => M.rel p (evalTerms M v ts)",
    "| .bottom => False\n  | .eq t1 t2 => evalTerm M v t1 = evalTerm M v t2\n  | .atom p ts => M.rel p (evalTerms M v ts)"
)

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
      simp [h, h1, h2, h3]"""

lift_new = """  | .var n =>
    unfold liftTerm evalTerm updateEnv
    split
    · rfl
    · rename_i h
      have h1 : ¬(n + 1 < c) := by omega
      have h2 : ¬(n + 1 = c) := by omega
      have h3 : n + 1 - 1 = n := by omega
      simp [h, h1, h2, h3]"""
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
        simp [h3]"""

subst_new = """  | .var n =>
    by_cases h1 : n = c
    · have h2 : ¬(n < c) := by omega
      simp [substTerm, evalTerm, updateEnv, h1, h2]
    · by_cases h3 : n < c
      · have h4 : ¬(n > c) := by omega
        simp [substTerm, evalTerm, updateEnv, h1, h3, h4]
      · have h4 : n > c := by omega
        have h5 : ¬(n - 1 < c) := by intro hlt; omega
        have h6 : ¬(n - 1 = c) := by intro heq; omega
        simp [substTerm, evalTerm, updateEnv, h1, h3, h4, h5, h6]"""
content = content.replace(subst_old, subst_new)

# Fix replaceAt_soundness
cases_old = """    cases f <;> simp only [getAt?, replaceAt, evalFormula] at hGet ⊢ <;> try contradiction
    · have h := ih hGet v; tauto
    · have h := ih hGet v; tauto
    · have h := ih hGet v; tauto"""
cases_new = """    cases f <;> simp only [getAt?, replaceAt, evalFormula] at hGet ⊢ <;> try contradiction <;> { have h := ih hGet v; tauto }"""
content = content.replace(cases_old, cases_new)

with open('FOL/Semantics.lean', 'w', encoding='utf-8') as f:
    f.write(content)
