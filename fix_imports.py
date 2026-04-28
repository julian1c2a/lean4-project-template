import os
import re

replacements = {
    r'\bimport FOL\.Semantics\b': 'import FOL.Semantics.Basic',
    r'\bimport FOL\.Soundness\b': 'import FOL.MetaTheory.Soundness',
    r'\bimport FOL\.Tactics\b': 'import FOL.Tactics.Basic',
    r'\bimport FOL\.Tactics2\b': 'import FOL.Tactics.Solver',
    r'\bimport FOL\.Completeness\b': 'import FOL.MetaTheory.Completeness',
    r'\bimport FOL\.Compactness\b': 'import FOL.MetaTheory.Compactness',
    r'\bimport FOL\.Deduction\b': 'import FOL.ProofSystem.Deduction',
    r'\bimport FOL\.Metamath\.Semantics\b': 'FOL.Metamath.Semantics', # If there are any stray ones
}

for root, _, files in os.walk('FOL'):
    for f in files:
        if f.endswith('.lean'):
            path = os.path.join(root, f)
            with open(path, 'r', encoding='utf-8') as file:
                content = file.read()
            
            new_content = content
            for old, new in replacements.items():
                new_content = re.sub(old, new, new_content)
            
            if new_content != content:
                with open(path, 'w', encoding='utf-8') as file:
                    file.write(new_content)
                print(f"Updated imports in {path}")
