import subprocess
import sys

try:
    with open('FOL/Semantics.lean', 'r', encoding='utf-8') as f:
        content = f.read()

    # Fix possible botched replacements from race condition
    bad_rule = '''theorem rule_soundness {D : Type} (M : Model D) (v M v A ↔ evalFormula M v B := by
  cases h
  simp only [evalFormula]
  apply Iff.intro
  · intro h1 h2 h3; exact h1 h3 h2
  · intro h1 h2 h3; exact h1 h3 h2'''
  
    old_rule = '''theorem rule_soundness {D : Type} (M : Model D) (v : Nat → D) {A B : Formula} (h : LocalRule A B) :
    evalFormula M v A ↔ evalFormula M v B := by
  cases h
  simp only [evalFormula]
  tauto'''

    new_rule = '''theorem rule_soundness {D : Type} (M : Model D) (v : Nat → D) {A B : Formula} (h : LocalRule A B) :
    evalFormula M v A ↔ evalFormula M v B := by
  cases h
  simp only [evalFormula]
  apply Iff.intro
  · intro h1 h2 h3; exact h1 h3 h2
  · intro h1 h2 h3; exact h1 h3 h2'''

    content = content.replace(bad_rule, new_rule)
    content = content.replace(old_rule, new_rule)
    
    content = content.replace('| .forall f1 ih =>', '| «forall» f1 ih =>')
    content = content.replace('| .ex f1 ih =>', '| ex f1 ih =>')
    
    content = content.replace('<;> { have h := ih hGet v; tauto }', '<;> { have h := ih hGet v; rw [h] }')

    with open('FOL/Semantics.lean', 'w', encoding='utf-8') as f:
        f.write(content)

    print('Semantics.lean updated. Running lake build...')
    result = subprocess.run(['lake', 'build'])
    sys.exit(result.returncode)
except Exception as e:
    print(e)
    sys.exit(1)
