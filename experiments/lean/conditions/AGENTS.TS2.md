# AGENTS.md: CS9 condition TS2 (single agent)

Read `TASK.md` and `PROBLEMS.jsonl` first. Workspace: this directory. Budget: **8 hours** of wall clock. CPU: your
pinned cores (`nproc`).

## Structure
- You work **alone**. Do **not** call `rlm.spawn`, `rlm.create_session`, or the factory. No subagents.
- You may run several of your own processes in parallel within your cores (e.g. several Lean checks at once).
  A Lean check uses about 3-4 GB of RAM.

## Rules
- The ledger is append-only. Work only in this directory. Never try to modify `referee/`, `tools/` or `upstream/`.
- There is no network; do not try to work around that. Kill processes only by PID, never by name.
- **Progress notes:** append a short Turkish note to `PROGRESS.md` about every hour.
- **Honesty:** report only what the referee accepted.
