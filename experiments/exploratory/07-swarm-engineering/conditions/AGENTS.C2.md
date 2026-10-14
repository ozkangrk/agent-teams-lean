# AGENTS.md: CS3 condition C2 (swarm)

Read `TASK.md` first; it is the task specification. This directory (`work/C2/`) is your whole workspace.

## Structure for this condition
- You are the **orchestrator** of a swarm. Use `rlm.spawn` for parallel workstreams, **at most 4 subagents at once**.
  Suggested roles: profiler (nsys/ncu hotspot analysis), kernel engineers (one per hotspot), integrator/verifier.
- Subagents work in their own git branches or worktrees of `TensorFold/` (e.g. `git worktree add ../wt-<name>`), and
  the integrator merges into the main worktree. GPU jobs always go through the lock.
- Subagents report with `rlm.progress_note` and finish with `agent_message.send(..., receiver_role='parent')`. You verify their results with the referee before you accept them.

## Checking correctness and speed
- The referee is available to everyone: `python3 -I ../../referee/referee.py judge <worktree> --tag C2-<short>`.
  Exit 0 = correct (the speedup is in the JSON), 1 = incorrect or build failure, 2 = environment.
- Your run ends with an external completion gate that runs the referee on the main worktree's HEAD and compares it with `RESULT.md`.

## General rules
- **Ledger is append-only:** never delete, truncate or rewrite `ledger.jsonl`; only append lines. Record the referee's verdict for an attempt as a new line (correct true/false) instead of editing an old one.
- Work only inside `work/C2/`. You may read `../../referee/` (it is the referee's code) but never modify it, or
  `../../_gates`, or `../../models`.
- Wrap every GPU job in `flock /tmp/swarm-gpu.lock ...`, and run one GPU job at a time.
- **Ledger:** one line per attempt in `ledger.jsonl` (format in TASK.md), including failures.
- Commit to the `TensorFold/` worktree after every meaningful attempt (the commit message names the hypothesis). Keep
  the best correct state as HEAD at the end.
- Write short Turkish progress notes to `PROGRESS.md` every hour or so: what was tried, what worked, the current best.
- Do not download tools or binaries. Do not touch other users' processes, ComfyUI, or other projects.
- Honesty: report exactly what you measured. If you could not make it faster without breaking correctness, say so.
  A truthful null result is acceptable; a false claim is not.
