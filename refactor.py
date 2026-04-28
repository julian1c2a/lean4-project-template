import os
import re
import shutil

moves = {
    'FOL/Basic.lean': 'FOL/Syntax/Basic.lean',
    'FOL/ProofSystem/Tactics.lean': 'FOL/Tactics/Basic.lean',
    'FOL/ProofSystem/Tactics2.lean': 'FOL/Tactics/Solver.lean',
    'FOL/Theorems/Impl.lean': 'FOL/Theorems/Prop/Impl.lean',
    'FOL/Theorems/Neg.lean': 'FOL/Theorems/Prop/Neg.lean',
    'FOL/Theorems/Quantifiers.lean': 'FOL/Theorems/FOL/Quantifiers.lean',
    'FOL/Theorems/Eq.lean': 'FOL/Theorems/FOL/Eq.lean',
}

# Module replacements
replacements = {
    'FOL.Basic': 'FOL.Syntax.Basic',
    'FOL.ProofSystem.Tactics2': 'FOL.Tactics.Solver',
    'FOL.ProofSystem.Tactics': 'FOL.Tactics.Basic',
    'FOL.Theorems.Impl': 'FOL.Theorems.Prop.Impl',
    'FOL.Theorems.Neg': 'FOL.Theorems.Prop.Neg',
    'FOL.Theorems.Quantifiers': 'FOL.Theorems.FOL.Quantifiers',
    'FOL.Theorems.Eq': 'FOL.Theorems.FOL.Eq',
}

# Create dirs
for dest in moves.values():
    os.makedirs(os.path.dirname(dest), exist_ok=True)

# Move files
for src, dest in moves.items():
    if os.path.exists(src):
        shutil.move(src, dest)
        print(f"Moved {src} -> {dest}")

# Update imports in all lean files
for root, _, files in os.walk('FOL'):
    for f in files:
        if f.endswith('.lean'):
            path = os.path.join(root, f)
            with open(path, 'r', encoding='utf-8') as file:
                content = file.read()
            
            new_content = content
            for old_mod, new_mod in replacements.items():
                # Regex to match exact import module name
                new_content = re.sub(rf'\b{old_mod}\b', new_mod, new_content)
            
            if new_content != content:
                with open(path, 'w', encoding='utf-8') as file:
                    file.write(new_content)
                print(f"Updated imports in {path}")
