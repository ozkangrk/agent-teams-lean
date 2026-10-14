# CS5 task: hard construction problems (HorizonMath construction track)

You have a fixed time budget (see AGENTS.md) and a fixed set of CPU cores (your processes are pinned with `taskset`;
do not try to escape it). There is **no GPU**. The 10 instances below come from the HorizonMath benchmark
(arXiv:2603.15617). Most are **open**: the best known value is not known to be optimal, and frontier models rarely
improve them. Produce the best **verified** construction you can for each, written to `solutions/<instance>.json`.
The referee (`../../referee/verify.py`, Claude's code, read-only) checks them; run it any time:

    ../../referee/.venv/bin/python -I ../../referee/verify.py solutions            # all instances
    ../../referee/.venv/bin/python -I ../../referee/verify.py solutions --only vdw-2-7

## Instances (details and sources in `../../referee/records.json`)

**Group A: records held by AI systems or classical constructions (match or beat)**

| Instance | Problem | Goal | Best known | Solution format |
|---|---|---|---|---|
| `keich-128` | Thin-triangle Kakeya, N=128, δ=1/128. Slopes are fixed at a_i=i/128; triangle i has upper edge y=a_i x+b_i and lower edge y=a_i x+b_i−δ(1−x) for x∈[0,1] | **minimise** the area of the union of the 128 triangles | 0.1148103258 (AlphaEvolve). GPT-5.4 Pro reportedly reached ≈0.10915 | `{"intercepts": [b_0..b_127]}`, \|b_i\| ≤ 4 |
| `heilbronn-12` | 12 points in the unit square | **maximise** the smallest triangle area | 0.0325988586918197 | `{"points": [[x,y],...]}` with 0 ≤ x,y ≤ 1 exactly (areas are computed in exact rational arithmetic) |
| `tammes-15` | 15 points on the unit sphere S² | **maximise** the minimum angular separation, in degrees | 53.6578501299 | `{"points": [[x,y,z],...]}`; points are projected onto the sphere before scoring |
| `autocorr-c1` | First autocorrelation inequality: a non-negative step function on [−1/4,1/4] with n equal steps | **minimise** max(f*f)/(∫f)² | 1.5028503021 (TTT-Discover; earlier AlphaEvolve 1.5053, then 1.50317) | `{"heights": [...]}`, 10 ≤ n ≤ 100000, all ≥ 0 |

**Group B: open combinatorial records (beating one is a new mathematical result)**

| Instance | Problem | Goal | Best known | Solution format |
|---|---|---|---|---|
| `dts-7-5` | (7,5) difference triangle set: 7 rows of 6 integers, each row starting at 0 and strictly increasing; all within-row positive differences distinct across the whole set | **minimise** the scope (largest entry) | 112 | `{"rows": [[0,...],...]}` |
| `vdw-2-7` | 2-colouring of {0,…,n−1} with no monochromatic 7-term arithmetic progression | **maximise** n | 3703 (so W(2,7) > 3703) | `{"coloring": [0,1,...]}` |
| `cwcode-29-8-5` | 5-subsets of {0..28} with every pair of points in at most one block (constant-weight code A(29,8,5)) | **maximise** the number of blocks | 36 (upper bound 39) | `{"blocks": [[...5 ints],...]}` |
| `covering-13-7-4` | 7-subsets of {0..12} that cover every 4-subset | **minimise** the number of blocks | 30 (lower bound 28) | `{"blocks": [[...7 ints],...]}` |
| `bklc-68-15` | binary linear [68,15] code | **maximise** the minimum distance d | 24 (upper bound 26) | `{"generator_matrix": ["0101…" × 15 rows of 68 chars]}`, rank 15 |
| `ruler-10000` | B ⊆ {0..9999} such that every d in 1..9999 is a difference of two elements (sparse ruler) | **minimise** \|B\| | 174 | `{"basis": [...]}` |

Matching a record is good. **Beating one is the main goal.** Getting close (small `gap_rel`) still counts.

## Rules
- Only the referee's verdict counts. **Never edit `../../referee/`.** Exploiting the evaluator voids the instance.
- Use any algorithm (SAT/ILP solvers, simulated annealing, tabu search, algebraic and finite-field constructions,
  gradient methods, ...). Python packages from PyPI via `uv` go in your workspace's own venv (for example numpy,
  scipy, numba, python-sat, ortools). Do not download binaries outside PyPI.
- **Literature.** Read papers via the arXiv, OpenAlex or Crossref APIs. Do **not** download published solution
  files, certificates or coordinate tables (for example from HorizonMath, La Jolla, Brouwer, Grassl, or the
  spherical-codes tables) and submit them. Constructions must be produced by your own code in this workspace. Record
  every source you used for ideas in `ledger.jsonl`.
- **Long jobs.** Any job longer than 20 minutes must run as a background shell. A watchdog terminates foreground
  commands that block a session for more than 20 minutes.
- **Ledger (required).** One JSON line per attempt in `ledger.jsonl`, including failures:

  ```
  {"ts", "agent", "instance", "method", "score", "verified": true|false, "notes"}
  ```

- **Deliverables.**
  - The best solution files in `solutions/`.
  - The scripts that produced them.
  - `RESULT.md` with a JSON block of claimed scores per instance.
  - For any instance where the referee reports `beats_record: true`: a reproduction command in RESULT.md.

  The completion gate verifies the claims against the referee, and it **does not let you finish before the time
  budget is used**.
