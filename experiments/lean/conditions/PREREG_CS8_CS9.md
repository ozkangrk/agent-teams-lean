# CS8 and CS9 pre-registration: independent agents (CS8) and a replication of CS7 (CS9)
Written 2026-10-13 ~18:00 +03, before either run.

## Why
CS7 found TW (orchestrator + ≤6 workers) 16 vs TS (single agent) 10 on 100 post-cutoff Lean statements (one-sided
McNemar p=0.0156). Two problems remain:
1. **Compute confound.** TW used about 4× the tokens, so the gain may come from parallel attempts rather than from
   coordination.
2. **Integrity.** CS7 had a TS sandbox escape (D6) and a TW worker reading TS's session log (D8). Both gaps are now
   closed by `kernel_sandbox_v2.sh`, an allow-list root with a per-condition session directory and private PID
   namespace. See DEVIATIONS D8.

## Common to CS8 and CS9 (changes from CS7, identical for every condition)
- **Problems:** the same problem set, `cs7_set.jsonl` (100 statements), and the same sanitised overlay (upstream
  sources and OEIS library).
- **Unchanged:** the referee, the model (GLM-5.3, `--thinking high`) and the budget (8 h wall clock).
- **Sandbox:** `kernel_sandbox_v2.sh`, with a per-condition `PRIME_AGENT_SESSION_DIR` (`agent-sessions/<C>`) and the
  daemon socket under /run/user.
- **Task text:** `TASK.v2.md`, which is CS7's text with the stale "80 statements (OEIS, Erdős, Wikipedia)" sentence
  corrected to the actual 100-statement set (D7).
- **Supervisor:** runs as a transient scope, so its gate output is correct (D6). It stops the agent daemon after the
  15-min grace (CS7: workers ran past the deadline).
- **Watchdog:** descends through both bwrap layers (namespace init) to the kernel.
- **Harness:** the files are frozen in `conditions/gates_snapshot_cs8/` before launch.

## CS8: four independent single agents (2026-10-13 ~17:50 → ~01:50)
- **Conditions IA1–IA4:** four separate Prime Agent sessions. Each is identical to CS7's TS instructions
  (`AGENTS.IA.md`): one agent, no `rlm.spawn`.
  - Each has its own workspace, session directory, daemon, supervisor and watchdog.
  - They cannot see or message each other: the sandbox hides other workspaces and logs, and daemon sockets are
    hidden.
- **Resources matched to CS7's TW:**
  - all four share cores 0–8 (9 cores, as TW's whole team did) and one memory budget, slice `cs8-ia.slice` with
    MemoryHigh 20G / MemoryMax 28G, no swap;
  - k = 4 because it is closest to TW's measured token multiple (calls ×3.9, output ×4.5) and to TW's mean live agents
    (3.6 workers + orchestrator).
- **Score:** the **union** of statements accepted in any IA workspace (Claude's final referee re-run).

## CS9: replication of CS7 (next run, earliest 2026-10-14 ~07:00, at least 5 h after CS8 so the provider quota window has cleared)
- **Conditions:**
  - TS2 = CS7 TS (AGENTS.TS2.md), on cores **9–17**;
  - TW2 = CS7 TW (AGENTS.TW2.md, ≤6 workers), on cores **0–8**. The core sets are swapped relative to CS7.
- **Resources:** same memory limits as CS7 (20G/28G each). Run simultaneously, 8 h.

## Outcomes and tests (fixed now)
Final verdicts come from Claude's referee re-run after each deadline. No post-hoc exclusions; deviations are reported
as sensitivity analyses.

**R1 (replication, CS9):** TW2 > TS2. Exact one-sided McNemar on discordant pairs, α=0.05.
- **Pooled CS7+CS9:** one-sided binomial test on b7+b9 vs c7+c9.
- **Sensitivity:** pooled with CS7's D8-affected TW-only proofs (4) removed.

**C1 (coordination, primary):** TW2 vs IA-union. Two-sided exact McNemar, α=0.05, both runs under the v2 sandbox.
- **Interpretation rule** (fixed now):
  - TW2 significantly > union → coordination adds beyond independent parallel attempts.
  - Otherwise, no evidence that coordination adds.
  - The point estimate and Tango 95% CI are reported either way.
- **Secondary:** the same against CS7's TW (D8 caveat).

**C2 (parallelism):** IA-union > TS2 and IA-union > TS (CS7). One-sided exact McNemar.

**Descriptive:**
- per-agent counts IA1–IA4 (four extra single-agent replicates; variability of a single agent);
- expected union size for k = 1..4 (mean over subsets);
- duplication: statements solved by ≥2 IA agents;
- hourly-snapshot curves;
- tokens (calls, output) per condition and per accepted proof;
- **token-matched union:** IA-union restricted to proofs accepted (by snapshot) before IA's cumulative output tokens
  reached TW2's total;
- integrity scans (isolation, escape, ~/.prime access) for every condition.

## Known limitations
- CS8 and CS9 run on different days; the provider's latency and quota state may differ.
- k=4 independent agents get fewer cores each than TS had (9 shared vs 9 alone), the same total as TW.
- The provider quota is account-wide. CS9 (TS2+TW2) may hit it as CS7 did. This is symmetric between TS2 and TW2 and
  will be reported.
- Same Unix user. Process listings are no longer visible inside the sandbox (PID namespace).
