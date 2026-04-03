# Updating Lean and Mathlib

## What the repo uses today

- **Lean** — version in [`lean-toolchain`](../lean-toolchain) (for example Lean 4.8.0).  
- **Mathlib** — a specific release tag in [`Lakefile.lean`](../Lakefile.lean) (for example `v4.8.0`) so everyone gets the same library snapshot.

## How to move to newer versions

1. Pick a Mathlib release (or commit) that matches the Lean version you want. Check Mathlib’s own toolchain file at that revision.  
2. If you change Lean, update [`lean-toolchain`](../lean-toolchain).  
3. Change the Mathlib tag or revision in [`Lakefile.lean`](../Lakefile.lean).  
4. Run `lake update` and fix any breakages.  
5. Commit the configuration changes and the updated dependency lock file (`lake-manifest.json`) in one change set.

Do this in a dedicated branch so others can review and tests can run.
