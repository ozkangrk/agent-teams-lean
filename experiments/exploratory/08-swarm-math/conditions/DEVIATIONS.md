# CS4 protocol deviations (dated, append-only)

## D1 — 2026-10-11 ~17:55 +03: tool-call watchdog added to both conditions (owner-approved)
- **Observation.** At 17:14 S1 ran a foreground test inside its python tool:
  `brute(N)` = `itertools.product([1,-1], repeat=N)` for N in [8, 12, 16, 24, 40]. N=40 cannot finish (about 2^37
  iterations before the leading signs change). The session showed `isRunningTools` with no activity for 37 minutes,
  0 solutions, and about 1 core in use. The supervisor never nudged it, because it only nudges idle sessions.
- **Rule (identical for S1 and S2).** `_gates/watchdog.py --limit-min 20`. A session blocked in a single tool call for
  more than 20 minutes has that call's foreground commands terminated: direct children of its REPL kernel older than
  20 minutes. Harness background shells (`_prime_agent_gate`) are exempt. Every session in both conditions received
  the same announcement text. Actions are logged to `work/<C>/watchdog.log`.
- **Pre-check.** A dry run selected only S1 pid 502657. Even with a 1-minute limit it selected nothing in S2, whose long
  jobs all run as background shells.
- **Status at the time of the deviation (41 min in).** S2 had valid solutions for 7/7 instances, two of which matched
  the record. S1 had 0 solutions.
- **Analysis consequence.** S1's first ~45 min are reported separately as a "blocking-call failure". The paper must
  separate the effect of the swarm structure (fault isolation, parallel use of cores) from the effect of the missing
  harness timeout.

## Analysis note A1 — 2026-10-11 18:05 +03 (not a protocol change)
- S2 PROGRESS.md claims circles-26 "published record broken": 2.6359830823 > `best_known` 2.63598.
- The `best_known` value is a **truncated** lower bound ("2.63598+"), so `beats_record=true` here only means
  "exceeds the truncated published digits".
- The paper must report circles-26 (and circles-32, "2.939+") as **matching the published value to its printed
  precision**, not as a new record, unless a full-precision literature value is retrieved and actually exceeded.
- The referee is unchanged during the run.

## Analysis note A2 — 2026-10-11 19:05 +03 (observed event)
- S2 PROGRESS.md (written 19:03:29) contains hand-written timestamps in the future: "19:1x" for circles-32 2.93957,
  which actually happened at ~18:10 per solutions/ mtime, and "20:0x" for thomson-400 matching the record, which
  actually happened at 19:01:46 per the ledger.
- The scores themselves verify. The ledger `ts` fields are correct.
- **Interpretation:** narrative time-keeping errors by the orchestrator, not score fabrication.
- **Paper:** use ledger/mtime timestamps only; never PROGRESS.md times.
- Circles-32: S1 and S2 both exceed the truncated "2.939+" (2.93957...). Per A1, report this as "matched to printed
  precision".

## Analysis note A3 — 2026-10-11 19:30 +03 (referee reference-value error, Claude's)
- `records.json` lists autocorr-c1 `best_known` = 1.5040 attributed to AlphaEvolve. **This is wrong.**
- Literature progression:
  - Matolcsi–Vinuesa 1.50973
  - AlphaEvolve v1 1.5053 (Novikov et al. 2025)
  - AlphaEvolve v2 1.50317
  - ThetaEvolve 1.50314 (arXiv:2511.23473)
  - TTT-Discover **1.5028503020710076** (arXiv:2601.16175; the HorizonMath benchmark baseline, a 90,000-step
    certificate)
- The referee is not changed mid-run, because the gap only affects reporting.
- **Final analysis:** recompute `gap_rel` against 1.5028503020710076. S2's 1.50526 (19:01) is at the AlphaEvolve-v1
  level, about 1.6e-3 above the current state of the art.

## D2 — 2026-10-11 ~21:55 +03: single-threaded BLAS when the gate calls the referee (evaluation runtime only)
- **Observation.** With all 18 experiment cores busy, `referee/verify.py` on S2's solutions did not finish in 600 s.
  Run on one idle core, or with `OPENBLAS_NUM_THREADS=1`, it takes 1.1 s.
- **Cause.** Multi-threaded OpenBLAS (20 threads) thrashes under oversubscription.
- **Effect.** The completion gate (timeout 1800 s), and the supervisor nudges that run it, could time out and report
  spurious failures.
- **Change.** `_gates/cs4_gate.py` now runs the referee with OPENBLAS/OMP/MKL_NUM_THREADS=1. Scores are unchanged
  (same code, same arithmetic). The referee itself is untouched.
- **Check.** No supervisor nudge had fired so far (supervisor.log shows none), so no gate verdict was affected.

## Event E1 — 2026-10-11 22:39 +03: gate crashed on a non-numeric claim (gate robustness bug, Claude's)
- The supervisor nudge to S2 at 22:39:50 carried a Python traceback from `cs4_gate.py` line 29 (`float(c)`). S2's
  RESULT.md then held a non-numeric claim.
- S2 rewrote RESULT.md at 22:40:12, and all claims became numbers.
- The gate now reports "claim must be a plain number" instead of crashing. Scoring is unchanged.
