#!/bin/sh

before_hook() {
  USE_BRANCH=$1
  BRANCH_COMMIT=$2

  STASH_NAME="hook-stash-$(date +%s)"
  git stash save --quiet --keep-index --include-untracked "$STASH_NAME"

  if [ "$USE_BRANCH" = "1" ]; then
    CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
    TEMP_BRANCH="hook-temp-$(date +%s)"
    echo "Creating temporary branch $TEMP_BRANCH..."
    git checkout -b "$TEMP_BRANCH" "$BRANCH_COMMIT" >/dev/null 2>&1
  fi

  TEMP_FILE=$(mktemp) || {
    echo >&2 "Failed to create temporary file"
    exit 1
  }

  export STASH_NAME USE_BRANCH CURRENT_BRANCH TEMP_BRANCH TEMP_FILE

  trap after_hook EXIT INT TERM
}

after_hook() {
  local exit_code=$?

  if [ "$USE_BRANCH" = "1" ] && git rev-parse --verify "$TEMP_BRANCH" >/dev/null 2>&1; then
    git checkout "$CURRENT_BRANCH" >/dev/null 2>&1
    git branch -D "$TEMP_BRANCH" >/dev/null 2>&1
  fi

  if git stash list | grep -q "$STASH_NAME"; then
    git stash pop --quiet
  fi

  [ -n "$TEMP_FILE" ] && rm -f "$TEMP_FILE"

  if [ $exit_code -ne 0 ]; then
    exit $exit_code
  fi
}
