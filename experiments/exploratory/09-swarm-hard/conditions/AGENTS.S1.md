# AGENTS.md: CS5 condition S1 (single agent)

Read `TASK.md` first. Your workspace is `work/S1/`. Budget: **8 hours** of wall clock. CPU: the cores you are
pinned to (`taskset`; check with `nproc`). No GPU.

## Structure for this condition
- You work **alone**. Do **not** call `rlm.spawn`, `rlm.create_session`, or the factory. No subagents.
- You may still run several of your own processes in parallel within your cores (e.g. multiprocessing).

## Rules
- **Ledger is append-only:** never delete, truncate or rewrite `ledger.jsonl`; only append lines. Record the referee's verdict for an attempt as a new line (correct true/false) instead of editing an old one.
- Work only inside `work/S1/`. Read `../../referee/` but never modify it, or anything else outside your workspace.
- Use a workspace venv (`uv venv .venv`) for packages. No sudo. No binary downloads.
- Memory cap for this condition: 10 GiB (exceeding it kills the largest process). Keep compute inside your pinned cores. Do not spawn processes on other cores or try to escape the pinning.
- **Ledger:** one line per attempt in `ledger.jsonl` (format in TASK.md), including failures.
- **Progress notes:** append a short Turkish note to `PROGRESS.md` about every hour (best verified score per instance,
  what is being tried).
- **Honesty:** report only what the referee verified. A false claim fails the gate. A truthful partial result is fine.
