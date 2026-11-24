# nosorry-verify

Verification runs for [nosorry](https://github.com/nosorry-maths): each run of the `verify` workflow checks one
submitted Lean proof against its reviewed statement. Runs are started by the nosorry worker, never by pull requests.

**What a run does**
1. Takes the job's files (`Challenge.lean`, `Solution.lean`, `plan.json`) from a `jobs/<id>` branch, as data.
2. Installs the pinned Lean toolchain and formal-conjectures at the commit in `fc/FC_REV` (Mathlib from its cache).
3. Runs the same Lean stages as the nosorry worker (`verifier/run-plan.mjs`):
   compile the reference statement; compile the submission; compare statements, definitions and axioms in separate
   environments (`verifier/Compare.lean`); replay every declaration in the kernel (`leanchecker`).
4. Prints one line, `NOSORRY-RESULT <base64 JSON>`, that the worker reads; the verdict is decided by the worker.

**Isolation.** Submitted Lean can run code while it compiles, so every Lean command runs as a separate unprivileged
account in a transient systemd service: no network, read-only system, write access to its own output directory only,
memory and time limits, every leftover process killed at the end. The run's token is read-only and never reaches it.

**Changes** to this repository go through pull requests reviewed by an owner.
