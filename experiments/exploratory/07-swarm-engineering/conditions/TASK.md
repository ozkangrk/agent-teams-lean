# CS3 task: make TensorFold's Nemotron decode faster on this GB10, without changing what it says

## Objective
Increase **single-stream greedy decode throughput without drafts** (`serve --no-drafts --parallel 1`) for NVIDIA
Nemotron 3.5 Lightning 30B-A3B (MLX 4-bit, hybrid Mamba + MoE) on this DGX Spark (NVIDIA GB10, sm_121, 128 GB
unified memory, about 273 GB/s).

| Measure | Value |
|---|---|
| Baseline (pinned commit `56150e6`, measured by the referee) | see `referee/baseline/baseline.json`, ≈95 tok/s |
| Weights-only roofline | ≈135 tok/s (2.03 GB read per token) |
| Secondary, reported but not optimised for | decode with drafts; prefill tok/s on an 11k-token prompt |

## Where you work
- `TensorFold/`: a git worktree of TensorFold at `56150e6` (Zig 0.17.0 + CUDA 13; kernels in `zig/kernels/cuda/*.cu`,
  the engine in `zig/src/families/nemotron/cuda_*.zig`, `zig/src/native/cuda.zig`). Edit anything in it; commit often.
- **Build:**

  ```
  ~/.local/opt/zig-0.17.0/zig build -Dnvcc=/usr/local/cuda/bin/nvcc -Doptimize=fast --prefix <dir> -j16 fatbins install native
  ```

  It takes about 25 min cold and minutes incrementally. The binary lands in `<dir>/native/bin/tensorfold-native`.
- **Model:** use `../../models/ref` **read-only** (never pass `--slide`; never write into it).
- **Profilers:** `nsys`, `ncu` (in `/usr/local/cuda/bin`).
- **GPU discipline:** wrap **every** GPU job (server, benchmark, profiler) in `flock /tmp/swarm-gpu.lock <cmd>`. Never
  run two GPU jobs at once, and never kill processes you did not start.

## Correctness (non-negotiable)
On a fixed prompt suite, your build must produce the **same greedy tokens** as the baseline. A divergence is tolerated
only where the baseline's top-2 log-probs are within 0.10 nats (a near-tie flip). Before the first divergence, log-probs
must agree: mean |Δ| ≤ 0.02, max ≤ 0.25. Upstream CPU tests (`zig build test test-cuda-host test-server-cpu`) must
pass. A fast but wrong kernel is a failure.

## Forbidden (each one voids the result)
- Special-casing prompts, caching or replaying outputs, or skipping work based on the input text.
- Changing sampling, defaults, server flags, or the context/precision of the model's weights or activations beyond what
  the correctness rule tolerates.
- Changing anything outside `TensorFold/` and your notes, ledger and result files. **Never edit `referee/`, `_gates/`,
  or `models/`.**
- Downloading tools or binaries. Python packages come only from PyPI via `uv`, and only if needed.

The final evaluation runs on a **hidden** prompt set (correctness and speed) that you cannot see, so overfitting to the
visible suite does not pay.

## Ledger (required)
Append one JSON line per attempt to `ledger.jsonl`:

```
{"ts": ISO8601, "agent": name, "hypothesis": str, "files": [..], "commit": sha|null, "build": "ok|failed",
 "check": "referee|self", "verdict": path|null, "correct": bool|null, "decode_tok_s": float|null, "notes": str}
```

Include failed and abandoned attempts. The ledger is the main evidence of how the work was done.

## Deliverables (by the end of the time budget)
- `TensorFold/` committed: your best correct state as HEAD, with a clean worktree.
- `RESULT.md` with a JSON block holding your claim:

  ```json
  {"commit": "<sha>", "decode_tok_s": <float>, "speedup_decode": <float>, "correctness": "<how you know>"}
  ```

  Add a short description of what changed and why it is faster.
