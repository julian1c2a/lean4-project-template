import os
import re

path = 'FOL/MetaTheory/Completeness.lean'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

# Replace lemma with theorem
content = re.sub(r'\blemma\b', 'theorem', content)

# Replace `use X` with `apply Exists.intro X`
# Note: use [f] -> apply Exists.intro [f]
# use Γ -> apply Exists.intro Γ
# use Γ1 ++ Γ2 -> apply Exists.intro (Γ1 ++ Γ2)
# We can just match `use (.*)`
content = re.sub(r'^[ \t]*use\s+(.*)$', r'  apply Exists.intro (\1)', content, flags=re.MULTILINE)

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
print("Fixed Completeness.lean")
