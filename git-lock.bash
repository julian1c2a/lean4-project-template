#!/bin/bash
# git-lock.bash — File locking and freezing system for Lean 4 projects
# Prevents accidental edits to completed modules via git pre-commit hook.
#
# Two protection levels:
#
#   LOCK   — Temporary write-protection. Unlockable. Used during active development
#            to enforce the one-file-at-a-time protocol.
#
#   FREEZE — Permanent write-protection. A frozen module is considered complete and
#            immutable. It cannot be unlocked. All future additions must go in a
#            separate *Ext.lean file that imports this one and reopens its namespace.
#            Frozen status can only be reverted with 'thaw --confirm' in emergencies.
#
# Usage:
#   bash git-lock.bash lock   ProjectName/Module.lean   # temporary lock
#   bash git-lock.bash unlock ProjectName/Module.lean   # temporary unlock (blocked if frozen)
#   bash git-lock.bash freeze ProjectName/Module.lean   # permanent freeze (Complete -> Frozen)
#   bash git-lock.bash thaw   ProjectName/Module.lean --confirm  # emergency unfreeze
#   bash git-lock.bash list                             # show all locked and frozen files
#   bash git-lock.bash init                             # install/reinstall pre-commit hook
#
# Protocol — session:
#   1. Session start : run 'list'. Unlock only the target file.
#   2. Switching     : lock current file BEFORE unlocking the next.
#   3. Session end   : lock all modified files, commit locked_files.txt.
#   4. Completion    : freeze the module when it reaches Complete status.
#
# Protocol — extension of frozen modules:
#   - Never thaw a frozen module to add new content.
#   - Create ModuleExt.lean, import the frozen module, reopen its namespace.
#   - See AI-GUIDE.md section 21 for the full extension protocol.

LOCK_LIST="locked_files.txt"
FROZEN_LIST="frozen_files.txt"

# ── Helpers ───────────────────────────────────────────────────────────────────

is_frozen() {
    [ -f "$FROZEN_LIST" ] && grep -Fxq "$1" "$FROZEN_LIST"
}

is_locked() {
    [ -f "$LOCK_LIST" ] && grep -Fxq "$1" "$LOCK_LIST"
}

ensure_lists() {
    touch "$LOCK_LIST"
    touch "$FROZEN_LIST"
}

show_help() {
    echo "Usage: bash git-lock.bash [command] [file] [--confirm]"
    echo ""
    echo "Commands:"
    echo "  lock   <file>           Lock file (temporary, unlockable)"
    echo "  unlock <file>           Unlock file (blocked if frozen)"
    echo "  freeze <file>           Permanently freeze a completed module"
    echo "  thaw   <file> --confirm Emergency unfreeze (requires --confirm)"
    echo "  list                    Show all locked and frozen files"
    echo "  init                    Install/reinstall the pre-commit hook"
    echo ""
    echo "Frozen modules cannot be unlocked. Extend them via *Ext.lean files."
    echo "See AI-GUIDE.md section 21 for the extension protocol."
}

# ── Main ──────────────────────────────────────────────────────────────────────

if [ $# -eq 0 ]; then
    show_help
    exit 1
fi

COMMAND=$1
FILE=$2
FLAG=$3

ensure_lists

case $COMMAND in

    # ── lock ──────────────────────────────────────────────────────────────────
    lock)
        if [ -z "$FILE" ]; then
            # lock with no argument -> lock the lock list itself
            chmod a-w "$LOCK_LIST"
            echo "Lock: write permission removed for '$LOCK_LIST'."
            exit 0
        fi
        if [ ! -f "$FILE" ]; then
            echo "Error: '$FILE' does not exist."
            exit 1
        fi
        if ! is_locked "$FILE"; then
            echo "$FILE" >> "$LOCK_LIST"
            echo "Added '$FILE' to $LOCK_LIST."
        else
            echo "'$FILE' was already in the lock list."
        fi
        chmod a-w "$FILE"
        if is_frozen "$FILE"; then
            echo "Frozen (permanent): $FILE"
        else
            echo "Locked: $FILE"
        fi
        ;;

    # ── unlock ────────────────────────────────────────────────────────────────
    unlock)
        if [ -z "$FILE" ]; then
            chmod u+w "$LOCK_LIST"
            echo "Unlocked: '$LOCK_LIST'."
            exit 0
        fi
        if is_frozen "$FILE"; then
            echo "ERROR: '$FILE' is permanently frozen and cannot be unlocked."
            echo "  Frozen modules are immutable. To add content, create an extension:"
            EXT_NAME="$(dirname "$FILE")/$(basename "${FILE%.lean}")Ext.lean"
            echo "  -> $EXT_NAME  (imports this file, reopens its namespace)"
            echo "  See AI-GUIDE.md section 21 for the extension protocol."
            echo ""
            echo "  Emergency only: bash git-lock.bash thaw $FILE --confirm"
            exit 1
        fi
        if is_locked "$FILE"; then
            grep -Fv "$FILE" "$LOCK_LIST" > "${LOCK_LIST}.tmp"; mv "${LOCK_LIST}.tmp" "$LOCK_LIST"
            echo "Removed '$FILE' from $LOCK_LIST."
        else
            echo "Warning: '$FILE' was not in the lock list."
        fi
        if [ -f "$FILE" ]; then
            chmod u+w "$FILE"
            echo "Unlocked: $FILE"
        fi
        ;;

    # ── freeze ────────────────────────────────────────────────────────────────
    freeze)
        if [ -z "$FILE" ]; then
            echo "Error: specify a file to freeze."
            echo "Usage: bash git-lock.bash freeze <file>"
            exit 1
        fi
        if [ ! -f "$FILE" ]; then
            echo "Error: '$FILE' does not exist."
            exit 1
        fi
        # Add to lock list if not already there
        if ! is_locked "$FILE"; then
            echo "$FILE" >> "$LOCK_LIST"
            echo "Added '$FILE' to $LOCK_LIST."
        fi
        # Add to frozen list
        if ! is_frozen "$FILE"; then
            echo "$FILE" >> "$FROZEN_LIST"
            echo "Added '$FILE' to $FROZEN_LIST."
        else
            echo "'$FILE' was already frozen."
        fi
        chmod a-w "$FILE"
        echo ""
        echo "FROZEN (permanent): $FILE"
        echo "  This module is considered complete and immutable."
        echo "  To add new content, create:"
        EXT_NAME="$(dirname "$FILE")/$(basename "${FILE%.lean}")Ext.lean"
        echo "  -> $EXT_NAME"
        echo "  that imports this file and reopens its namespace."
        echo "  See AI-GUIDE.md section 21 for the extension protocol."
        ;;

    # ── thaw ──────────────────────────────────────────────────────────────────
    thaw)
        if [ -z "$FILE" ]; then
            echo "Error: specify a file to thaw."
            echo "Usage: bash git-lock.bash thaw <file> --confirm"
            exit 1
        fi
        if [ "$FLAG" != "--confirm" ]; then
            echo "ERROR: Emergency operation. Requires explicit confirmation."
            echo "  Run: bash git-lock.bash thaw $FILE --confirm"
            echo ""
            echo "  WARNING: Thawing a frozen module breaks the immutability guarantee."
            EXT_NAME="$(dirname "$FILE")/$(basename "${FILE%.lean}")Ext.lean"
            echo "  Consider creating $EXT_NAME instead."
            exit 1
        fi
        if ! is_frozen "$FILE"; then
            echo "Note: '$FILE' was not frozen."
        else
            grep -Fv "$FILE" "$FROZEN_LIST" > "${FROZEN_LIST}.tmp"; mv "${FROZEN_LIST}.tmp" "$FROZEN_LIST"
            echo "Removed '$FILE' from $FROZEN_LIST."
        fi
        if is_locked "$FILE"; then
            grep -Fv "$FILE" "$LOCK_LIST" > "${LOCK_LIST}.tmp"; mv "${LOCK_LIST}.tmp" "$LOCK_LIST"
            echo "Removed '$FILE' from $LOCK_LIST."
        fi
        if [ -f "$FILE" ]; then
            chmod u+w "$FILE"
        fi
        echo ""
        echo "WARNING: '$FILE' has been thawed."
        echo "  IMPORTANT: Update REFERENCE.md to reflect the changed module status."
        echo "  IMPORTANT: Document why the module was modified after freezing."
        ;;

    # ── list ──────────────────────────────────────────────────────────────────
    list)
        echo "=== Frozen Modules (permanent, in $FROZEN_LIST) ==="
        if [ -s "$FROZEN_LIST" ]; then
            while IFS= read -r f; do
                [ -n "$f" ] && echo "  [frozen] $f"
            done < "$FROZEN_LIST"
        else
            echo "  (none)"
        fi
        echo ""
        echo "=== Locked Files (temporary, in $LOCK_LIST) ==="
        HAS_LOCKED=0
        if [ -s "$LOCK_LIST" ]; then
            while IFS= read -r f; do
                [ -z "$f" ] && continue
                if ! is_frozen "$f"; then
                    echo "  [locked] $f"
                    HAS_LOCKED=1
                fi
            done < "$LOCK_LIST"
        fi
        [ $HAS_LOCKED -eq 0 ] && echo "  (none)"
        ;;

    # ── init ──────────────────────────────────────────────────────────────────
    init)
        touch "$LOCK_LIST"
        touch "$FROZEN_LIST"
        HOOK_DIR=".git/hooks"
        HOOK_FILE="$HOOK_DIR/pre-commit"
        if [ ! -d ".git" ]; then
            echo "Error: not in a git repository root."
            exit 1
        fi
        echo "Installing hook at $HOOK_FILE..."
        cat > "$HOOK_FILE" << 'HOOKEOF'
#!/bin/bash
# Pre-commit hook: blocks commits touching locked/frozen files, warns about sorry.

LOCK_LIST="locked_files.txt"
FROZEN_LIST="frozen_files.txt"
STAGED_FILES=$(git diff --cached --name-only)
ERROR=0

# ── Check 1: Frozen files (permanent — never allow) ───────────────────────────
if [ -f "$FROZEN_LIST" ]; then
    while IFS= read -r FROZEN_FILE; do
        [ -z "$FROZEN_FILE" ] && continue
        if echo "$STAGED_FILES" | grep -Fqx "$FROZEN_FILE"; then
            echo "ERROR FROZEN (immutable): $FROZEN_FILE"
            EXT="$(dirname "$FROZEN_FILE")/$(basename "${FROZEN_FILE%.lean}")Ext.lean"
            echo "  This module is permanently frozen. Create an extension instead:"
            echo "  -> $EXT"
            echo "  See AI-GUIDE.md section 21 for the extension protocol."
            ERROR=1
        fi
    done < "$FROZEN_LIST"
fi

# ── Check 2: Locked files (temporary — unlock first) ─────────────────────────
if [ -f "$LOCK_LIST" ]; then
    while IFS= read -r LOCKED_FILE; do
        [ -z "$LOCKED_FILE" ] && continue
        # Skip if already caught by frozen check
        if [ -f "$FROZEN_LIST" ] && grep -Fxq "$LOCKED_FILE" "$FROZEN_LIST"; then
            continue
        fi
        if echo "$STAGED_FILES" | grep -Fqx "$LOCKED_FILE"; then
            echo "ERROR LOCKED: $LOCKED_FILE"
            echo "  Unlock first: bash git-lock.bash unlock $LOCKED_FILE"
            ERROR=1
        fi
    done < "$LOCK_LIST"
fi

# ── Check 3: New sorry statements (warning only) ──────────────────────────────
SORRY_COUNT=0
for F in $STAGED_FILES; do
    if [[ "$F" == *.lean ]] && [ -f "$F" ]; then
        N=$(grep -c 'sorry' "$F" 2>/dev/null || true)
        N="${N//[^0-9]/}"   # strip any non-numeric chars (MSYS safety)
        N="${N:-0}"
        if [ "$N" -gt 0 ] 2>/dev/null; then
            echo "WARNING: $N sorry in $F"
            SORRY_COUNT=$((SORRY_COUNT + N))
        fi
    fi
done
[ "$SORRY_COUNT" -gt 0 ] && echo "  Total sorry statements in staged files: $SORRY_COUNT"

if [ $ERROR -eq 1 ]; then
    exit 1
fi
exit 0
HOOKEOF
        chmod +x "$HOOK_FILE"
        echo "Lock/freeze system initialized. Pre-commit hook installed."
        echo "  Tracking: $LOCK_LIST (locks), $FROZEN_LIST (frozen modules)"
        echo "  Run 'bash git-lock.bash init' again after pulling to reinstall the hook."
        ;;

    *)
        show_help
        exit 1
        ;;
esac
