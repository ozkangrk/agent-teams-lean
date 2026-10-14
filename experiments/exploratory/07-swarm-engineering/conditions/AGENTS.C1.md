# AGENTS.md: CS3 condition C1 (single agent)

Read `TASK.md` first; it is the task specification. This directory (`work/C1/`) is your whole workspace.

## Structure for this condition
- You work **alone**. Do **not** call `rlm.spawn`, `rlm.create_session`, or the factory. No subagents.

## Checking correctness and speed
- The referee is available to you: `python3 -I ../../referee/referee.py judge TensorFold --tag C1-<short>`.
  It builds your worktree, checks correctness, benchmarks under the GPU lock, and writes `../../verdicts/<time>-<tag>/verdict.json`.
  Exit 0 = correct (the speedup is in the JSON), 1 = incorrect or build failure, 2 = environment.
- Your run ends with an external completion gate that runs the referee on your HEAD and compares it with your `RESULT.md` claim.

## General rules
- Work only inside `work/C1/`. You may read `../../referee/` (it is the referee's code) but never modify it, or
  `../../_gates`, or `../../models`.
- Wrap every GPU job in `flock /tmp/swarm-gpu.lock ...`, and run one GPU job at a time.
- **Ledger:** one line per attempt in `ledger.jsonl` (format in TASK.md), including failures.
- Commit to the `TensorFold/` worktree after every meaningful attempt (the commit message names the hypothesis). Keep
  the best correct state as HEAD at the end.
- Write short Turkish progress notes to `PROGRESS.md` every hour or so: what was tried, what worked, the current best.
- Do not download tools or binaries. Do not touch other users' processes, ComfyUI, or other projects.
- Honesty: report exactly what you measured. If you could not make it faster without breaking correctness, say so.
  A truthful null result is acceptable; a false claim is not.
