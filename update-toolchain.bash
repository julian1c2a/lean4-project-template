#!/bin/bash
# update-toolchain.bash — Update lean-toolchain to a new version and verify build
#
# Usage:
#   bash update-toolchain.bash             # Auto-detects latest version from GitHub
#   bash update-toolchain.bash v4.29.0     # Explicit version
#
# On success: commits the updated lean-toolchain file.
# On failure: restores the previous version.

set -e

if [ $# -eq 0 ]; then
    echo "Fetching latest Lean 4 release from GitHub..."
    # Requires curl and jq
    LATEST_JSON=$(curl -s https://api.github.com/repos/leanprover/lean4/releases/latest)
    TARGET_VERSION=$(echo "$LATEST_JSON" | grep -oP '"tag_name": "\K(.*)(?=")')
    
    if [ -z "$TARGET_VERSION" ]; then
        echo "Failed to fetch latest version."
        exit 1
    fi
    
    echo "Latest version is $TARGET_VERSION"
    echo "Release notes:"
    echo "----------------------------------------"
    echo "$LATEST_JSON" | grep -oP '"body": "\K(.*)(?=")' | sed 's/\\r\\n/\n/g' || echo "See GitHub for full release notes."
    echo "----------------------------------------"
else
    TARGET_VERSION="$1"
fi

NEW_VERSION="leanprover/lean4:$TARGET_VERSION"
OLD_VERSION=$(cat lean-toolchain)

if [ "$NEW_VERSION" == "$OLD_VERSION" ]; then
    echo "Already on the latest version: $OLD_VERSION"
    exit 0
fi

echo "Updating toolchain: $OLD_VERSION → $NEW_VERSION"
echo "$NEW_VERSION" > lean-toolchain

echo "Running lake build..."
if lake build; then
    echo ""
    echo "✅ Build passed with $NEW_VERSION"
    git add lean-toolchain
    git commit -m "chore: update lean toolchain to $TARGET_VERSION"
    echo "✅ Committed lean-toolchain update."
else
    echo ""
    echo "❌ Build failed. Restoring previous toolchain: $OLD_VERSION"
    echo "$OLD_VERSION" > lean-toolchain
    exit 1
fi
