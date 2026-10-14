# AGENTS.md: CS5 condition S3 (large hybrid swarm)

Read `TASK.md` first. Your workspace is `work/S3/`. Budget: **8 hours** of wall clock. CPU: the cores you are
pinned to (`taskset`; check with `nproc`). No GPU.

## Structure for this condition
- You are the **orchestrator** of a large **hybrid** swarm. Two model pools exist; you decide how to use them.
  - **Up to 8 GLM-5.3 subagents** at once: the default model of `rlm.spawn`, same as yours.
  - **Up to 4 local Qwen3.8-Flash-Next subagents** at once:
    `rlm.spawn(..., model="tensorfold/qwen3.8-flash-next")`.
    - Served on this machine by TensorFold, with 4 parallel slots (a 5th call waits for a free slot) and a
      131k-token context.
    - Somewhat slower per turn, and it uses no provider quota.
- At most **12 subagents running at once in total**, in at most two levels.
  - For example, up to 4 **team leads**, one per group of related instances (continuous geometry, autocorrelation,
    designs and codes, colourings and rulers).
  - Each lead runs a few **workers** on competing methods or seeds.
  - `rlm.factory` runs (`foreach` fan-out) are allowed if they respect the same limits.
- **All agents share the same pinned cores and a 10 GiB memory cap for this condition.** More agents does not mean
  more compute: give each lead a core allowance, and let workers spend their time on **ideas, analysis and short
  experiments**, with few long background jobs. Exceeding the memory cap kills the largest process.
- The GLM provider rate-limits concurrent requests (about 20 per account, shared with other runs on this machine).
  Prime Agent retries rate-limited calls.
- Subagents report with `rlm.progress_note` and finish with `agent_message.send(..., receiver_role='parent')`. Leads
  merge into their own subdirectory. You merge the best **verified** solutions into `solutions/`.
- Keep a short `TEAM.md`: which agent (and which model) works on what, with its core allowance. Update it when you
  re-assign work.

## Rules
- **Ledger is append-only:** never delete, truncate or rewrite `ledger.jsonl`; only append lines. Record the referee's verdict for an attempt as a new line (correct true/false) instead of editing an old one.
- Work only inside `work/S3/`. Read `../../referee/` but never modify it, or anything else outside your workspace.
- Use a workspace venv (`uv venv .venv`) for packages. No sudo. No binary downloads.
- Keep compute inside your pinned cores. Do not spawn processes on other cores or try to escape the pinning.
- **Ledger:** one line per attempt in `ledger.jsonl` (format in TASK.md), including failures. Use the `agent` field
  for the agent's role name.
- **Progress notes:** append a short Turkish note to `PROGRESS.md` about every hour (best verified score per instance,
  what is being tried).
- **Honesty:** report only what the referee verified. A false claim fails the gate. A truthful partial result is fine.
