#!/bin/bash
# check-sorry.bash — Find all sorry statements in .lean files
#
# ⚠️ Cuenta `sorry` como TOKEN: excluye `sorryAx`, las menciones entre backticks
#    (`sorry` en prosa y docstrings) y las lineas de comentario. Contarlas daba falsos
#    positivos — un modulo de metaprogramacion que habla de `sorry` no tiene sorries.
#
# Usage:
#   bash check-sorry.bash           # check all .lean files
#   bash check-sorry.bash staged    # check only staged files (for CI)
#   bash check-sorry.bash Module    # check files matching pattern

set -e

MODE="${1:-all}"
TOTAL=0
FILES_WITH_SORRY=0

if [ "$MODE" = "staged" ]; then
    LEAN_FILES=$(git diff --cached --name-only | grep '\.lean$' || true)
elif [ "$MODE" = "all" ]; then
    LEAN_FILES=$(find . -name "*.lean" ! -name "_template.lean" ! -path "./.lake/*" | sort)
else
    LEAN_FILES=$(find . -name "*${MODE}*.lean" ! -path "./.lake/*" | sort)
fi

if [ -z "$LEAN_FILES" ]; then
    echo "No .lean files found."
    exit 0
fi

echo "=== sorry report ==="
while IFS= read -r FILE; do
    [ -z "$FILE" ] && continue
    [ ! -f "$FILE" ] && continue
    COUNT=$(grep -cE '(^|[^a-zA-Z_`])sorry([^a-zA-Z_`]|$)' "$FILE" 2>/dev/null | head -1 || true)
    COUNT="${COUNT//[^0-9]/}"
    COUNT="${COUNT:-0}"
    if [ "$COUNT" -gt 0 ] 2>/dev/null; then
        echo ""
        echo "📄 $FILE ($COUNT sorry)"
        grep -nE '(^|[^a-zA-Z_`])sorry([^a-zA-Z_`]|$)' "$FILE" | sed 's/^/   /'
        TOTAL=$((TOTAL + COUNT))
        FILES_WITH_SORRY=$((FILES_WITH_SORRY + 1))
    fi
done <<< "$LEAN_FILES"

echo ""
if [ "$TOTAL" -eq 0 ]; then
    echo "✅ No sorry found."
else
    echo "⚠️  Total: $TOTAL sorry in $FILES_WITH_SORRY file(s)."
    exit 1
fi
