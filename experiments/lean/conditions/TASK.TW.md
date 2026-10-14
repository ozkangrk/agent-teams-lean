# CS7: Lean 4 proofs of known results (formal-conjectures, `research solved`)

Every statement in `PROBLEMS.jsonl` is a result that is **known to be true** (proved in the mathematical
literature) but has no Lean proof in google-deepmind/formal-conjectures. There are 80 statements (OEIS, Erdős
problems, Wikipedia). Your goal is to produce as many complete, kernel-checked Lean 4 proofs as possible within the
time budget. Some statements are short computations or elementary arguments; others are research-level.

Your tools run **without network access**. You can read:
- your workspace
- `../../upstream/formal-conjectures` (statements; Mathlib sources under `.lake/packages/mathlib/`)
- `../../library/oeis/A??????.json`: the OEIS entry of each sequence (formulas, comments, programs, references,
  terms)
- `../../tools/` and `../../referee/`

All of these are read-only except your workspace.

## Strategy (your choice)
- Triage: read each statement, its definitions and (for OEIS) `../../library/oeis/A??????.json`, and estimate
  tractability.
- Throughput matters: every accepted proof counts equally. Record your triage in `TRIAGE.md`.

## Submission
For problem `<id>`, write `proofs/<id>.lean`:

```lean
import <module>
theorem swarm_proof : <statement> := by ...
```

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
