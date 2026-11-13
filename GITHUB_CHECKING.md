# Checking the proof on GitHub

The repository includes a GitHub Actions workflow for independent kernel
verification.

- `lean-toolchain` pins Lean 4.20.0.
- `lakefile.lean` registers every flat source module.
- `lake-manifest.json` pins the resolved Mathlib dependencies.
- `.github/workflows/lean-kernel-check.yml` builds the complete project and
  runs both axiom audits.

## Uploading

1. Create an empty GitHub repository.
2. Extract this ZIP.
3. Upload the **contents** of the extracted `bounded_zermelo` directory to the
   repository root, including the hidden `.github` directory.
4. Commit and push the files.
5. Open the repository's **Actions** tab and select
   **Lean kernel verification**.

The workflow is green only if all three commands succeed:

```text
lake build
lake env lean KernelAudit.lean
lake env lean FoundationFreeKernelAudit.lean
```

For both the original and Foundation-free endpoints, the expected axiom list
is:

```text
[propext, Classical.choice, Quot.sound]
```

There must be no `sorryAx` in the output.

The first run may take several minutes while GitHub downloads Lean and the
pinned Mathlib cache. Generated `.lake` files should not be committed.

## Optional command-line upload

After replacing the repository URL:

```sh
git init
git add .
git commit -m "Add Foundation-free finite axiomatization proof"
git branch -M main
git remote add origin https://github.com/OWNER/REPOSITORY.git
git push -u origin main
```
