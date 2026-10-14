# CS7 pre-registration: proofs per hour, single agent vs swarm (written 2026-10-12, before launch)

## Question
At equal compute, equal wall-clock time, the same model and the same tools, does a swarm of agents produce more
**kernel-checked Lean proofs** than a single agent on a large set of independent problems?

## Problem set (fixed before launch: `conditions/cs7_set.jsonl`)
- 80 statements from google-deepmind/formal-conjectures @79222608, tagged `research solved`. Each is a result known
  in the literature but without a Lean proof in the repository (proof = `sorry`), so every statement is true and
  provable.
- Sampling, with seed 20261013:
  - stratified into 40 OEIS, 30 ErdosProblems and 10 Wikipedia/WrittenOnTheWallII
  - at most one statement per source file
  - statement ≤ 300 characters, no `answer(sorry)`
  - analytic and asymptotic statements excluded by the same regex filter as O1 (limits, densities, measure, logs,
    filters, …), so the set focuses on discrete and algebraic mathematics
  - the 8 pilot statements excluded
- The referee checks each proof against the upstream constant (`type_of%`) with an axiom whitelist.

## Conditions (run simultaneously, 8 h each)

| | TS (single agent) | TW (swarm) |
|---|---|---|
| Agents | 1, no `rlm.spawn` | orchestrator + ≤ 6 concurrent subagents |
| Model | GLM-5.3 (z.ai) | GLM-5.3 only |
| CPU | cores 0-8 | cores 9-17 |
| Memory | MemoryHigh 20G, MemoryMax 28G, no swap, OOMPolicy=continue | same |

Shared:
- Kernel sandbox: no network; other workspaces hidden; referee, upstream, tools and library read-only.
- The same TASK text, offline OEIS library, referee, supervisor (with a 30-min pre-check) and 20-min watchdog.

## Outcomes
- **Primary (H1):** the number of the 80 statements with a referee-accepted proof in the final workspace
  (`proofs/<id>.lean`, re-run by Claude after the deadline). One-sided hypothesis: TW > TS.
  - **Test:** exact one-sided McNemar (binomial) test on the discordant pairs, α = 0.05.
  - Reported with the paired difference and an exact 95 % CI.
- **Secondary:**
  - **H2:** cumulative accepted proofs versus time, from Claude's hourly referee snapshots of `proofs/` (an
    hourly-snapshot time series).
  - **H3:** GLM tokens per accepted proof, counted from session files with subagents included.
  - **H4:** rule-integrity events, from the isolation scan and network attempts (the sandbox should make these
    zero).
  - **H5:** overlap. Which statements does each condition solve? Is either a superset?

## Rules for the experimenter (Claude)
- No post-hoc exclusions.
- **Harness fault:** if a condition is lost to a harness fault, resume it with the lost time added (CS5 D3
  precedent) and report this.
- **Interventions:** only symmetric ones, sent to both conditions with identical text and logged.
- **Messages to agents:** only for rule violations, and then to both conditions.
- No problem-specific hints.

## Known limitations (stated in advance)
- Both conditions run as the same Unix user, so command lines are visible in `ps` across conditions. File access
  across conditions is blocked by the sandbox.
- **Single model and single run:** no replication within this night. Power is limited: with about 10 % vs 20 %
  solve rates, n=80 gives modest power.
  - A null result will be reported as inconclusive, not as "no effect".
  - Replication (swapped core sets) is planned if the effect is borderline.
- z.ai rate limits are account-wide. With 8 concurrent sessions the run stays below the measured limit (≈15-25).

## Amendment A1 — 2026-10-12 21:30 +03, before launch (owner question about training-data contamination)
**Problem set replaced.** `conditions/cs7_set.jsonl` now holds **100 statements that flipped from `research open`
to `research solved` in formal-conjectures between 2026-08-01 and 2026-10-12**, taken from the git history
(commits that change `category research open` to `research solved`).
- These are known to be true and provable, and their resolutions were published after GLM-5.3's training data
  (assumption: training cutoff before August 2026). The informal and formal solutions should therefore not be
  recallable.
- Filters as before:
  - still `sorry` in the repository
  - no `answer(sorry)`
  - analytic/asymptotic regex excluded
  - ≤ 300 characters
  - ≤ 2 statements per file
  - seed 20261013
- Composition:
  - by source: 42 OEIS, 18 Erdős, 11 WOTW-II, 8 arXiv, 8 Wikipedia, 5 Paper, 3 Green, 2 Other
  - by resolution month: 34 Aug, 45 Sep, 21 Oct
- The previous literature-solved set is kept as `cs7_set_v1_literature.jsonl` (not run).

**Leak-free views.** Both conditions see:
- **sanitized upstream sources:** every comment and docstring and every `formal_proof … at "url"` clause removed;
  zero URLs remain. They are mounted over `upstream/formal-conjectures/FormalConjectures`; the compiled .oleans are
  untouched, so the referee is unchanged.
- **a sanitized OEIS library:** lines dated 2026 or mentioning proved, disproved, counterexample, Adamczewski,
  OEIS Open or arXiv 26xx are removed (132 lines dropped).

There is still no network.

**Added secondary analysis (H6):** solve rates by resolution month (Aug, Sep, Oct), as a sensitivity check on the
cutoff assumption.

Everything else is unchanged: conditions, 8 h, equal cores and memory, primary test.

## Amendment A2 — 2026-10-12 23:15 +03, before launch (infrastructure only; identical for both conditions)
- **Watchdog:** a call blocked inside the kernel for 20 min or more (pure-Python loop or `await`) is now aborted
  through the daemon's own `abort` command (what Esc does). Then the standard notice "WATCHDOG: your tool call
  exceeded 20 minutes and was aborted (TASK.md rule). Continue; run long jobs in the background." is sent.
  Background shells are never touched. The kernel ignores a raw SIGINT. The flow was verified end to end
  (2026-10-12 23:07).
- **Robustness:** the tmux server (`-L research`), supervisor and watchdog now run as their own systemd units, so
  a Claude desktop app restart cannot kill them (CS6 D3).
- **Start:** launch moved earlier, to about 23:20, because O1 ended early (D3). Duration is still 8 h.
