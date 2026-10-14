# CS6 main run O1: open OEIS conjectures in Lean 4

Every statement in `PROBLEMS.jsonl` is an **open conjecture**: tagged `research open` in google-deepmind/
formal-conjectures, and added to the repository after Feb 2026, i.e. after the large published AI sweeps. There are
94 statements over 83 sequences. A complete, kernel-checked **proof or disproof** of any one of them is a new
mathematical result. Most will resist; one or two successes would be an excellent outcome.

Your tools run **without network access**. You can read:
- your workspace
- `../../upstream/formal-conjectures` (statements; Mathlib sources under `.lake/packages/mathlib/`)
- `../../library/oeis/A??????.json`: the OEIS entry of each sequence (formulas, comments, programs, references,
  terms)
- `../../tools/` and `../../referee/`

All of these are read-only except your workspace.

## Strategy (your choice, but think about it)
- **Triage first.** For each statement read its definitions and the OEIS entry, and compute many terms numerically
  (Python is available). Estimate tractability. Typical good targets:
  - a sequence given by a recurrence or a closed form, where the conjecture follows from a formula provable by
    induction (periodicity, factorisation, parity, divisibility)
  - finite checks reducible to `decide`-sized computations
  - **counterexamples:** if the numbers contradict the conjecture, prove the negation
- Spend effort where the evidence says a proof (or disproof) is within reach, and record the triage in `TRIAGE.md`.

## Submission
For problem `<id>`, write `proofs/<id>.lean`:

```lean
import <module>
theorem swarm_proof : <statement> := by ...          -- proves the conjecture
-- or
theorem swarm_disproof : ¬ (<statement>) := by ...   -- refutes it (e.g. an explicit counterexample)
```

Exactly one of the two per file.

## Checking
- Compile a file: `../../tools/lean.sh proofs/<id>.lean`.
- Official verdict, which you can also run yourself:

  ```
  python3 -I ../../referee/check.py --module '<module>' --theorem <theorem> --proof $PWD/proofs/<id>.lean
  ```

- Acceptance requires:
  - no `sorry`/`admit`/`axiom`/`native_decide`/metaprogramming/`set_option debug.*`
  - the submission compiles in a sandbox
  - the proof matches the **upstream** constant's type (or its negation)
  - axioms limited to propext, Classical.choice and Quot.sound
- Note: `native_decide` is forbidden; large finite checks must go through `decide` or explicit lemmas.

## Rules
- Only the referee's verdict counts. Never try to modify `referee/`, `tools/`, `upstream/` or `library/`.
- **Ledger (required).** One JSON line per attempt in `ledger.jsonl`, failures included:

  ```
  {"ts", "agent", "id", "approach", "accepted": true|false|null, "notes"}
  ```

- **Deliverables.** Accepted files in `proofs/`, `TRIAGE.md`, and `RESULT.md` that **must contain exactly this JSON
  block**:

  ```json
  {"accepted": ["<id>", ...]}
  ```

  The completion gate re-runs the referee on each claimed id, and it does not let you finish before the time budget
  is used.
