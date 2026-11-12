# Checking this proof on GitHub

The repository already contains everything required for an independent
GitHub Actions check:

- `lean-toolchain` pins Lean 4.20.0;
- `lakefile.lean` declares the project and Mathlib dependency;
- `lake-manifest.json` pins the resolved dependency commits;
- `.github/workflows/lean-kernel-check.yml` builds the complete project and
  then runs `KernelAudit.lean`.

## Uploading

1. Create an empty GitHub repository.
2. Extract this ZIP.
3. Upload **the contents of the extracted directory**, including the hidden
   `.github` directory, to the repository root. Do not upload only the ZIP as
   one opaque file.
4. Commit the files to any branch. The workflow runs on every push and pull
   request.
5. Open the repository's **Actions** tab and select
   **Lean kernel verification**.

The check is green only if both workflow steps succeed:

```text
lake build
lake env lean KernelAudit.lean
```

The final step prints the exact types and axiom dependencies of the six main
theorems. The expected dependency list for each is:

```text
[propext, Classical.choice, Quot.sound]
```

There must be no `sorryAx` in that output.

The first run may take several minutes because GitHub must download Lean and
the pinned Mathlib dependencies. Later runs normally reuse the action's
`.lake` cache.

## Optional command-line upload

If Git and the GitHub CLI are installed locally, run these commands from the
extracted directory after replacing the repository URL:

```sh
git init
git add .
git commit -m "Add kernel-verified nine-axiom BZ proof"
git branch -M main
git remote add origin https://github.com/OWNER/REPOSITORY.git
git push -u origin main
```

Do not commit the local `.lake` directory; it is a generated build cache and
is excluded by `.gitignore`.
