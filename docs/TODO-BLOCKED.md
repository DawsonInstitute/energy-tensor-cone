# TODO-BLOCKED.md: Tasks Requiring User Action

**Project**: Convex Cone of Energy Tensors under AQEI

## Blocked Tasks

**9. Git log fixes (BLOCKED - Requires User Confirmation)**

Some early commits in the repository have incorrect author/email:
```
Author: Your Name <you@example.com>
```

These should be changed to:
```
Author: Arcticoder <10162808+arcticoder@users.noreply.github.com>
```

**Why Blocked**: This requires rewriting git history using `git filter-branch` or `git rebase`, which:
1. Changes commit hashes
2. Can cause issues if others have cloned the repository
3. Requires force-pushing to remote
4. Is potentially destructive if done incorrectly

**Recommended Action**: User should review and execute manually:

```bash
# Option 1: Using git filter-branch (deprecated but simple)
git filter-branch --env-filter '
if [ "$GIT_COMMITTER_EMAIL" = "you@example.com" ]; then
    export GIT_COMMITTER_NAME="Arcticoder"
    export GIT_COMMITTER_EMAIL="10162808+arcticoder@users.noreply.github.com"
fi
if [ "$GIT_AUTHOR_EMAIL" = "you@example.com" ]; then
    export GIT_AUTHOR_NAME="Arcticoder"
   export GIT_AUTHOR_EMAIL="10162808+arcticoder@users.noreply.github.com"
fi
' -- --all

# Option 2: Using git-filter-repo (recommended, requires installation)
# Install: pip install git-filter-repo
# Then use: git filter-repo --commit-callback [see git-filter-repo docs]

# After fixing, force push (CAUTION):
# git push --force-with-lease origin main
```

**Alternative**: Leave history as-is if timestamps and attribution are not critical.

**Status**: Awaiting user decision
**Date Blocked**: February 7, 2026
