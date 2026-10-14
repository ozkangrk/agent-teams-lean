# AGENTS.md: CS6 pilot condition P1 (swarm)

Read `TASK.md` and `PROBLEMS.jsonl` first. Workspace: this directory. Budget: **3 hours** of wall clock. CPU: your
pinned cores (`nproc`).

## Structure
- You are the **orchestrator** of a swarm. Use `rlm.spawn` for parallel workstreams, **at most 6 subagents at once**,
  all on the default model.
  - For example, one prover per problem or group of problems, or competing provers on one problem.
  - Subagents may spawn their own helpers, but the total running at any time stays ≤ 6.
- Lean checks use about 3-4 GB of RAM and a few cores each, so coordinate how many run in parallel.
- Subagents report with `rlm.progress_note` and finish with `agent_message.send(..., receiver_role='parent')`. You
  keep `proofs/` and `RESULT.md` consistent with referee verdicts.

## Rules
- The ledger is append-only. Work only in this directory. Never try to modify `referee/`, `tools/` or `upstream/`.
- There is no network; do not try to work around that. Kill processes only by PID, never by name.
- **Progress notes:** append a short Turkish note to `PROGRESS.md` about every 30 minutes.
- **Honesty:** report only what the referee accepted.
