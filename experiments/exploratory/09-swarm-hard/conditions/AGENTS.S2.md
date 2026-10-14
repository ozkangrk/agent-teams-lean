# AGENTS.md: CS5 condition S2 (swarm)

Read `TASK.md` first. Your workspace is `work/S2/`. Budget: **8 hours** of wall clock. CPU: the cores you are
pinned to (`taskset`; check with `nproc`). No GPU.

## Structure for this condition
- You are the **orchestrator** of a swarm. Use `rlm.spawn` for parallel workstreams, **at most 4 subagents at once**.
  For example, one agent per group of related instances (continuous geometry, autocorrelation, designs and codes, colourings and rulers), or competing methods on the most promising open instance.
- All agents share the same pinned cores, so coordinate the compute: give each a core budget.
- Subagents report with `rlm.progress_note` and finish with `agent_message.send(..., receiver_role='parent')`. You merge the best **verified** solutions into `solutions/`.

## Rules
- **Ledger is append-only:** never delete, truncate or rewrite `ledger.jsonl`; only append lines. Record the referee's verdict for an attempt as a new line (correct true/false) instead of editing an old one.
- Work only inside `work/S2/`. Read `../../referee/` but never modify it, or anything else outside your workspace.
- Use a workspace venv (`uv venv .venv`) for packages. No sudo. No binary downloads.
- Memory cap for this condition: 10 GiB (exceeding it kills the largest process). Keep compute inside your pinned cores. Do not spawn processes on other cores or try to escape the pinning.
- **Ledger:** one line per attempt in `ledger.jsonl` (format in TASK.md), including failures.
- **Progress notes:** append a short Turkish note to `PROGRESS.md` about every hour (best verified score per instance,
  what is being tried).
- **Honesty:** report only what the referee verified. A false claim fails the gate. A truthful partial result is fine.
