# CS6 pilot: Lean 4 proofs of formal-conjectures statements

You have a fixed time budget (see AGENTS.md) and fixed CPU cores. Your tools run **without network access**, and you
can see only your own workspace, the read-only `../../upstream/formal-conjectures` (statements, plus a Mathlib build at
`v4.33.1`), `../../tools/` and `../../referee/`.

Goal: produce complete, kernel-checked Lean 4 proofs for as many of the problems in `PROBLEMS.jsonl` as possible.
Each line gives `id`, `module`, `theorem` (fully qualified name), `file` (statement source under
`../../upstream/formal-conjectures/`) and the statement text.
- 4 warm-up statements are small computations.
- 8 statements are results that are **known in the mathematical literature** but have no Lean proof in the
  repository. Some are research-level.
- A statement of the form `answer(True) ↔ P` is proved by proving that iff, with `answer(True)` reducing to `True`.

## Submission format
For problem `<id>`, write `proofs/<id>.lean`:

```lean
import <module>          -- exactly the module from PROBLEMS.jsonl
-- optional: your own auxiliary lemmas/defs (top level or inside a namespace you close)
theorem swarm_proof : <the statement, with the definitions of the upstream file> := by
  ...
```

You may `open` the upstream namespace to write the statement conveniently. The referee does **not** trust your
restatement: it checks your proof against the type of the upstream constant itself (`type_of% @<theorem>`).

## Checking
- Compile a file: `../../tools/lean.sh proofs/<id>.lean`. Mathlib and formal-conjectures are importable.
- Official verdict, which you can also run yourself:

  ```
  python3 -I ../../referee/check.py --module '<module>' --theorem <theorem> --proof $PWD/proofs/<id>.lean
  ```

- Acceptance requires:
  - no `sorry`/`admit`/`axiom`/`native_decide`/metaprogramming/`set_option debug.*`
  - the submission compiles in a sandbox
  - the proof matches the upstream statement's type
  - `#print axioms` lists only propext, Classical.choice and Quot.sound
- Useful tactics: `simp`, `omega`, `decide`, `norm_num`, `nlinarith`, `positivity`, `aesop`, `exact?`, `apply?`,
  `rw?`, `grind`. To search Mathlib, grep the sources under `../../upstream/formal-conjectures/.lake/packages/mathlib/`.

## Rules
- Only the referee's verdict counts. `referee/`, `tools/` and `upstream/` are read-only.
- **Ledger (required).** One JSON line per attempt in `ledger.jsonl`:

  ```
  {"ts", "agent", "id", "approach", "accepted": true|false, "notes"}
  ```

  Include failed attempts with the referee's reason.
- **Deliverables.** Accepted proofs in `proofs/`, and `RESULT.md` with a JSON block
  `{"accepted": ["<id>", ...]}`. The completion gate re-runs the referee on every claimed id, and it does not let
  you finish before the time budget is used.
