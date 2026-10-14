# CS4 task: improve constructions for well-known extremal problems

You have a fixed time budget (see AGENTS.md) and a fixed set of CPU cores (your processes are pinned with `taskset`;
do not try to escape it). There is **no GPU** for this task. Produce the best **verified** construction you can for each
of the 7 instances below. Write each one to `solutions/<instance>.json`. The referee (`../../referee/verify.py`, Claude's
code, read-only) checks them; run it any time:

    ../../referee/.venv/bin/python -I ../../referee/verify.py solutions

## Instances (reference values in `../../referee/records.json`)
| Instance | Problem | Goal | Solution format |
|---|---|---|---|
| `thomson-282`, `thomson-400`, `thomson-470` | Thomson problem: N unit charges on the unit sphere | **minimise** the Coulomb energy Σ 1/‖xᵢ−xⱼ‖ | `{"points": [[x,y,z], ...]}` with exactly N points, each with \|‖x‖−1\| ≤ 1e-9 |
| `circles-26`, `circles-32` | N disjoint circles inside the unit square | **maximise** the sum of radii | `{"centers": [[x,y], ...], "radii": [...]}`; overlap and boundary are checked in **exact rational arithmetic** on your floats, so leave no float slack |
| `autocorr-c1` | First autocorrelation inequality: a non-negative step function on [−1/4, 1/4] with n equal steps | **minimise** max(f*f) / (∫f)² | `{"heights": [h_0, ..., h_{n-1}]}`, all hᵢ ≥ 0, n ≤ 100000 |
| `discrepancy-2` | Erdős discrepancy: a ±1 sequence whose sums over every homogeneous progression d, 2d, …, kd stay in [−2, 2] | **maximise** the length N | `{"signs": [1, -1, ...]}` |

Best known values to aim for (from the literature; details in records.json):

| Instance | Best known |
|---|---|
| Thomson N=282 | 37147.294418462 |
| Thomson N=400 | 75582.448512213 |
| Thomson N=470 | 104822.886324279 |
| circles n=26 | ≥ 2.63598 |
| circles n=32 | ≥ 2.939 |
| autocorrelation C1 | 1.5040 (AlphaEvolve) |
| discrepancy C=2 | 1160 (a proven maximum) |

Matching or beating any of these is a strong result. Improving on simple baselines matters too: the score is how close
you get.

## Rules
- Only the referee's verdict counts. **Never edit `../../referee/`.**
- Exploiting the evaluator voids the instance. Examples: numerical tricks, values outside the allowed format, solutions
  that only pass because of floating-point slack.
- You may use any algorithm, and Python packages from PyPI via `uv` (for example scipy, numba, or a SAT solver such as
  `python-sat`) inside your workspace's own venv. Do not download binaries outside PyPI.
- Literature: you may read papers via the arXiv, OpenAlex or Crossref APIs. Do **not** download published coordinate
  files or solutions (for example tables of optimal configurations) and submit them. Constructions must be produced by
  your own code in this workspace. Record any source you used for ideas in `ledger.jsonl`.
- **Ledger (required).** One JSON line per attempt in `ledger.jsonl`:

  ```
  {"ts", "agent", "instance", "method", "score", "verified": true|false, "notes"}
  ```

  Include failures.
- **Deliverables.** The best solution files in `solutions/`, plus `RESULT.md` with a JSON block containing your claimed
  score per instance. The completion gate verifies the claims against the referee, and it **does not let you finish
  before the time budget is used**: keep improving until then.
