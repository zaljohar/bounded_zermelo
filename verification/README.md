# Five-lock verification (candidate CI setup)

This adds an opt-in local command and a separate GitHub Actions workflow to the
adaptive snapshot e462decaaae595d3991e8e265718956f5326a3df. No existing file is
changed. The existing Lean 4.20.0 workflow remains authoritative for its own
build. The new workflow builds a disposable copy using Lean/Mathlib v4.35.0.
Migration compatibility and all checker results remain untested until CI runs.

## Run

Create a branch from adaptive and add the files from the patch at the repository
root (including the hidden .github directory). Push, open Actions, and select
Five-lock verification (Lean 4.35). On Linux with elan, Python 3, bubblewrap and
network access, the equivalent command is `bash verification/run.sh`.

The official `lake comparator --paranoid --json` checks the four named solution
endpoints against independently stored statement/definition text in Challenge.lean
and permits only propext, Classical.choice and Quot.sound. It requires Lean's
kernel and leanchecker-paranoid, con-leche, con-ron, nanoda and lean4lean. No
checker is optional, no sandbox bypass is used, and failure is not green.
Challenge has four intentional `sorry` placeholders, not part of the solution.
The definitions were copied from the original repository, not independently
invented; review them against the intended mathematical axioms. The challenge
imports Mathlib only, never a solution module. Keep this specification fixed
and review changes to it and CI separately. The root toolchain and manifest
are untouched; the temporary workspace resolves Mathlib v4.35.0 and saves its
resolved manifest with the evidence. For adversarial verification, use a trusted
checkout of the challenge and configuration, and pin all dependencies and CI
actions to reviewed immutable revisions.

The artifact contains the JSON report, stderr, setup log, resolved manifest,
and status. The job reports aggregate status; individual checker outcomes are
in the official report, not separate simulated green indicators. A setup/build
failure or timeout is not a proof rejection. The theorem targets only the four
Foundation-free endpoints, not all auxiliary lemmas or the older endpoint as
independent targets. The imported proof dependencies are checked as needed.

References: https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/

Current status: NOT RUN. The preparation environment has no Lean/elan and
cannot download them; neither migration nor actual checking has been tested.
