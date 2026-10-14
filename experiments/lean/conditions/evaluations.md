# CS6 pilot P1 — evaluation (Claude, 2026-10-12 ~14:55 +03)

**Setup:**
- 3 h (11:33-14:33 + grace), cores 0-11, orchestrator + ≤6 GLM-5.3 subagents.
- Kernel sandbox: no network; workspace-only view; referee, upstream and toolchain read-only.
- Referee: `type_of%` against the upstream constant, axiom whitelist, static scan.

**Result (`work/P1/final_verdict.json`, Claude's independent referee run):**

| Group | Accepted |
|---|---|
| Warm-up (4) | 3: Erdos138 W1=1, W2=3; Erdos1074 EHSNumbers_init. PillaiPrimes_init was accepted mid-run, then the file was overwritten into a non-compliant state |
| Literature-solved (8) | **1**: OEIS A113250 (odd-indexed terms are squares), via the closed form a(n)=4^n·q(n) with q 6-periodic. The proof is genuine; a public external Lean proof exists, but there was no network, so it was not accessible |

**Below the pre-set threshold** (≥2/8 literature-solved).

**Gate: FAIL (format).** RESULT.md had tables but no ```json {"accepted": …}``` block, despite the 14:03 pre-check.

**Partial progress (not accepted):**
- **698:** large compiled infrastructure (Vandermonde, an Erdős–Szekeres bound, a Kummer iff lemma, the h-reduction).
  A single `sorry` remains: the core of Bergman's 2011 bound.
- **812:** a reduction compiles; one open piece remains (reconstructing the BEFS89 device).
- **1050:** three independent routes all stopped at the same denominator-growth barrier; the infrastructure lemmas
  compile.
- **650:** CRT parametrisation with 6 numerically verified candidates; no Lean proof.
- **966, 1036, 206:** skipped (they need Gallai, Hales–Jewett or Shelah-level machinery).

**Assessment of GLM-5.3 in Lean 4 (this harness):**
- **Good at:** finite and order-theoretic formalisation (sInf arguments, pigeonhole, decide/omega), and elementary
  number theory by closed form plus induction.
- **Also good at:** building large partial infrastructures and numerical exploration.
- **Bottleneck:** reconstructing deep literature arguments offline (Bergman, Borwein, Burr–Erdős–Faudree–Schelp).
- **Behaviour:** honest negative reports; self-corrected identities.

**Events:**
- **D1:** the watchdog killed the orchestrator's kernel (bwrap tree); fixed 13:17.
- Two early subagents (ramsey812, borwein2) ended silently around 12:2x. There is no OOM and no watchdog record;
  the cause is unexplained. The orchestrator respawned them.
- A proof file regressed after acceptance (Pillai).

**Cost:** 878 GLM calls, 4.0M input + 54.1M cache-read, 2.12M output tokens (12 subagent session files).


# CS6 main run O1 — evaluation (Claude, 2026-10-12 22:55 +03)

**Setup:**
- 94 open OEIS statements (added after 2026-02-15, analytic statements filtered).
- Orchestrator + ≤6 GLM-5.3 subagents, cores 0-17, sandboxed (no network).
- Planned for 12 h; stopped at 7 h (D3) after the orchestrator had been frozen since 16:50 (D2).

**Triage (ran 15:52-16:49, done by the orchestrator alone):**
- Numerics over all 94 statements; counterexample hunts found none.
- Notable insight: A017666's conjecture implies that no odd perfect numbers exist. This is "proof impossible"
  without settling that problem.

**Accepted (Claude's referee):**
- R1 A060841 conjecture1 (19:17, 518 lines).
- R2 A046969 conjecture1 (19:37, 1470 lines).
- Both are valid and faithful to the OEIS conjecture, but **neither is novel**: others had resolved them days
  before (jackburrus/breakthroughs; JustinSunPrize #4914). The repository's `research open` tag lagged.

**Partial:** A000224 has the ⟸ direction and several cases compiled; the case of n with three or more prime factors
is open.

**Process findings:**
- **Orchestrator bottleneck:** a 6 h in-kernel loop left 8 subagent messages unprocessed (D2).
- **Novelty-check protocol:** formal-conjectures GitHub, TheJustinSunPrize/awards, OEIS Open, OEIS entry.

**Cost:** 1131 GLM calls; 1.90M output tokens; 201M cache-read tokens.

# CS7 — single agent (TS) vs orchestrator–worker team (TW), proofs per 8 h (Claude, 2026-10-13 ~08:00 +03)
Pre-registered in `PREREG_CS7.md` (+ A1 post-cutoff set and sanitized views, + A2 infrastructure).
- **Set:** 100 statements flipped open→solved in formal-conjectures between 2026-08-01 and 2026-10-12.
- **Run:** 23:08 → 07:08, GLM-5.3 for both conditions, 9 cores each.
- **Analysis:** `conditions/analyze_cs7.py`, output in `conditions/cs7_analysis.json`.
- **Final verdicts:** Claude's referee re-run in `work/<C>/final_verdict.json`. Both completion gates PASS
  (`final_gate.txt`), and each RESULT.md matches its referee-accepted set exactly.

**Team actually used:**
- 1 orchestrator plus 6 long-lived workers, with no depth-2 agents.
- At most 6 workers ran at once; the time-weighted mean was **3.6 live workers** (first-to-last session event; 6 workers for the first ~3.3 h, then 3, then 2).
- Terminology for the paper: an *orchestrator–worker multi-agent team*, not a "swarm".

**H1 (primary): TW 16 vs TS 10 of 100.**

| | Count |
|---|---|
| Solved by both | 10 |
| Solved by TW only (b) | 6 |
| Solved by TS only (c) | 0 |

- **Test:** exact one-sided McNemar, **p = 0.0156** (2⁻⁶). The hypothesis TW > TS is supported at α = 0.05.
- **Paired difference:** +6.0 points.
  - Exact conditional 95 % CI [0.5, 6.0]: Clopper–Pearson on the discordant split. Its upper bound is capped by
    construction.
  - Tango score 95 % CI [2.1, 12.5]: unconditional sensitivity check.
- **Cluster sensitivity** (89 source files; the sampler allowed ≤ 2 statements per file): TW-only 5 files, TS-only 0,
  p = 0.031.
- **TW-only statements:**
  - OEIS-103425
  - OEIS-129365 c1
  - OEIS-237271 conjecture_5
  - OEIS-237271 observation_carmichael
  - OEIS-93456
  - WOTW-II GraphConjecture200

**H2 (time; pre-registered measure = Claude's hourly referee snapshots):**

| Snapshot | ~43-45 min | ~104-107 min | ~164-187 min | ~283 min | ~343 min | end |
|---|---|---|---|---|---|---|
| TS | 0 | 8 | 9 | 9 | 10 | 10 |
| TW | 10 | 12 | 15 | 15 | 16 | 16 |

- **Ledgers (agent-reported):** first referee acceptance at minute 12 (TW) vs 63 (TS).
- **Last proofs:** both conditions got their last proof just after the quota outage (TS 3625 at about 04:48, TW
  about 04:14).
- **Correction (2026-10-13 ~11:00):** an earlier version of this section used proof-file creation (birth) times and
  claimed "TW 11 proofs at 30 min". That was **wrong**: files can be created early and completed hours later; TS's
  3625 file is an example. Use the snapshots.
- **Mechanism visible in the logs:**
  - The single orchestrator blocked twice inside its kernel early on (watchdog aborts at 23:33 and 00:00, 21 min
    each), so all work stopped.
  - In TW, blocked calls (7 aborts, 3 of them in the orchestrator) stall one agent at a time.
  - Both conditions lost about 1 h to the shared quota outage (D5).

**H3 (cost, GLM-5.3, subagents included):**

| | Calls | Prompt tokens (incl. cache) | Output tokens | Per proof |
|---|---|---|---|---|
| TS | 509 | 50.1M | 0.54M | 51 calls, 5.0M prompt, 54k output |
| TW | 2010 | 146.7M | 2.45M | 126 calls, 9.2M prompt, 153k output |

- TW used about 4× the calls and 4.5× the output tokens for 1.6× the proofs.
- The 6 extra proofs cost about 1500 calls (about 16M prompt and 320k output tokens each).
- **Compute was matched on wall-clock time, cores and model, not on tokens.** The paper must address this; see the
  planned controls below.

**H4 (integrity):**
- Isolation scans: 0 cross-workspace accesses in both conditions.
- Network: 0 attempts in both conditions.
- **TS:** 1 sandbox-escape episode (D6). It used the tmux socket to run commands outside the sandbox, killed and
  replaced its supervisor, and gained no scoring advantage. TW: 0 escapes.
- Harness faults affecting both conditions (D4-D6) are documented. In particular, the supervisor's gate output was
  wrong for both until 05:56.
- TW workers kept writing `scratch/` until 07:38, after the 07:23 tmux close (daemon still alive). `proofs/` was
  unchanged after 07:08, so scoring is unaffected. Cleanup should stop the agent scopes at the deadline.

**H5 (overlap):** TS ⊂ TW. Every statement the single agent proved, the team proved too.

**H6 (resolution month, sensitivity for the cutoff assumption):**

| Month resolved | n | TS | TW |
|---|---|---|---|
| Aug | 34 | 10 | 13 |
| Sep | 45 | 0 | 3 |
| Oct | 21 | 0 | 0 |

- All solves are in OEIS (TS 10/42, TW 15/42) plus one WOTW-II statement for TW. There were none in Erdős, arXiv,
  Wikipedia or papers.
- Within OEIS: August 20 → TS 10 / TW 12; September 20 → TS 0 / TW 3.
- **Interpretation:** the August concentration is confounded with difficulty.
  - Most August solves are statements added to formal-conjectures on Aug 12-20 and flipped to solved 2-11 days later
    (TS's 10: added Aug 13/20, solved Aug 15-24). Fast community resolutions suggest easy statements: sequence
    identities and recurrences, small-modulus facts.
  - Later flips (Sep/Oct) include Erdős, arXiv and harder OEIS items.
  - So month cannot separate "easier batch" from "possibly seen in training".
- The paper must report this as a limitation. The H1 comparison is paired, so any contamination affects both
  conditions equally and cannot by itself produce TW > TS.

**Conclusion:**
- In this pre-registered, contamination-controlled run, a small orchestrator–worker team (mean 3.6 live workers) proved
  significantly more post-cutoff Lean statements than a single agent with the same model, wall-clock time and cores.
- The team was also much faster: 10 accepted proofs at the first snapshot (about 45 min) against 0.
- It also used about 4× the tokens. Whether the gain comes from **coordination** or from **more parallel samples**
  is untested.

**Next:**
- **CS8:** k independent single agents, with the union scored at an equal token budget.
- **Replication** with swapped core sets.
- Hide the tmux and user-bus sockets in the sandbox; run supervisors as scopes.

# CS8 — four independent single agents (IA1–IA4) on the CS7 set (Claude, 2026-10-14 ~02:30 +03)
Pre-registered in `PREREG_CS8_CS9.md`.
- **Run:** 17:43 → 01:43; v2 allow-list sandbox, per-condition session directories.
- **Resources:** cores 0–8 shared by all four; one 20G/28G memory slice.
- **Records:** analysis in `conditions/analyze_cs8.py`, output in `conditions/cs8_analysis.json`; final verdicts are
  Claude's referee re-run on `work/IA*/proofs/`.
- **Harness:** the supervisors stopped the agent units at 02:00 (deadline + grace), and `proofs/` did not change after
  01:43 in any condition. The new stop step worked.
- **Gates:**
  - IA1 and IA4 PASS.
  - IA2: the gate crashed on file naming. Its proofs are not stored as `proofs/<id>.lean`; the referee accepts all 10
    claimed proofs through the snapshot's number mapping.
  - IA3: the gate crashed on RESULT.md format (claims written as dicts).
  - Both are deliverable-format failures only; scoring uses the referee re-run, as pre-registered.

**Results:**
- **Per agent:** IA1 14, IA2 10, IA3 14, IA4 8; mean 11.5. CS7 TS had 10, inside this range.
- **Union:** 16 of 100. The four agents proved 46 statements between them, but only 16 distinct ones.
  - 14 of the 16 were proved by ≥2 agents; 6 by all four.
  - Expected union for k = 1, 2, 3, 4: 11.5, 14.3, 15.5, 16.0, so returns diminish quickly.
- **New statement:** OEIS-129365-conjecture2, which neither CS7 condition proved.
- **CS7 TW-only statements:** the union contains 5 of the 6. That includes 3 of the 4 accepted after the D8 read
  (129365-c1, 237271-c5, 237271-obs), so independent agents with no access to anything also reach them.
- **C2 (union > CS7 TS):** union-only 6, TS-only 0, one-sided exact McNemar **p = 0.0156**. TS ⊂ union.
- **Union vs CS7 TW (two-sided, D8 caveat):**
  - TW-only 1 (WOTW-II GraphConjecture200), union-only 1 (129365-c2).
  - p = 1.0. Tango 95% CI for TW − union: [−4.6, +4.6] points.
  - **Equal coverage.**
- **Cost:** 3200 GLM calls and 3.68M output tokens (IA1 1.31M, IA2 0.68M, IA3 1.14M, IA4 0.54M), versus CS7 TW 2010
  calls and 2.45M. That is 1.6× the calls and 1.5× the output for the same coverage.
- **Token-matched (pre-registered, conservative):**
  - The four agents reached TW's 2.45M output tokens at 22:02.
  - The last snapshot before that point (21:12) shows **union 12**; the next one (22:12) shows 14. So at TW's token
    budget the union was 12–14, against TW's 16.
  - At TS's budget (0.54M, reached 18:48) the union was 3.
- **Time:** union by snapshot: 3 (28 min), 7 (1 h 28), 11 (2 h 28), 12, 14, 16 (5 h 28), then flat. CS7 TW had 10 at
  its first snapshot (45 min) and 16 by 5 h 44.
- **Integrity:** 3175 tool calls; 0 hits for other workspaces, other logs or sockets, harness, network, or earlier
  results. Watchdog: 11 aborts or terminations in total (IA1 1, IA2 4, IA3 1, IA4 5); all agents continued.

**Reading (before CS9):**
- Parallelism explains most of the team's advantage in *coverage*. Four uncoordinated copies of the single agent reach
  the team's 16 within the same 8 h.
- What coordination adds in CS7 is *efficiency*:
  - the same coverage at about two-thirds of the tokens;
  - much faster early progress;
  - little duplicated work (the four agents duplicated about 65% of their proofs).
- The primary coordination test (C1: TW2 vs union, both under the v2 sandbox) comes from CS9.

# CS9 — replication of CS7 (TS2 vs TW2) and the combined CS7–CS9 analysis (Claude, 2026-10-14 ~16:30 +03)
- **Run:** 07:11 → 15:11; v2 sandbox. TS2 on cores 9–17, TW2 (≤6 workers, 10 spawned in total) on cores 0–8.
- **Records:** analysis in `conditions/analyze_cs9.py`, output in `conditions/cs9_analysis.json`.
- **Deviations:**
  - D9: worker logs are stored in the global directory; measurement fixed.
  - D10: nested proof layout; snapshot fixed, CS7 and CS8 counts unchanged.
  - D11: provider quota stop at about 09:47. The owner reset the quota at about 10:15. Both conditions resumed through
    the standard nudge; TS2 lost about 45 min, TW2 about 15 min.
- **Gates:**
  - TS2 PASS.
  - TW2: the gate crashed on its nested layout, a deliverable-format failure. Scoring uses the referee re-run.
- **Integrity:** 2368 tool calls; 0 hits for other workspaces, other logs, harness, network or earlier results.
- **Watchdog:** TS2 2 aborts, TW2 10.

**R1 (replication of H1):**
- **Counts:** TW2 13, TS2 11. TS2 ⊂ TW2 again.
- **Discordant pairs:** TW2-only 2 (102371, 237271-c5), TS2-only 0.
- **Test:** exact one-sided McNemar p = 0.25; Tango 95% CI [−1.8, +7.0] points. **Not significant on its own.**

**Pooled CS7 + CS9:**
- **Overall:** b = 8, c = 0, one-sided p = 0.0039.
- **Sensitivity** (CS7's 4 D8-affected TW-only proofs removed): b = 4, c = 0, p = 0.0625.

**C1 (primary coordination test): TW2 vs IA-union (CS8).**
- **Counts:** TW2 13, union 16.
- **Discordant pairs:** TW2-only 1 (102371); union-only 4 (93456, 70823, 129365-c1, 129365-c2).
- **Test:** two-sided p = 0.375; Tango 95% CI for TW2 − union [−9.0, +1.9] points.
- **Pre-registered reading:** **no evidence that coordination adds beyond independent parallel attempts.** The point
  estimate favours the uncoordinated union.
- **Secondary:** CS7 TW vs union 16:16, p = 1.0.

**C2 (parallelism):**
- union > TS2: 5 vs 0, p = 0.031;
- union > CS7 TS: 6 vs 0, p = 0.016.

**Cost:**

| | TW2 | TS2 | CS7 TW | IA total |
|---|---|---|---|---|
| Calls | 1807 | 697 | 2010 | 3200 |
| Output tokens | 2.45M | 0.65M | 2.45M | 3.68M |

- The team costs 3.7× the single agent's output tokens.
- **Token-matched:** at TW2's budget of 2.45M output tokens, the IA union stood at 12–14, against TW2's 13. Equal.
- **CS7's apparent efficiency advantage of coordination did not replicate.** CS7 TW reached 16 and TW2 reached 13 on
  the same budget.

**Single-agent variability (6 runs on the same set):** TS 10, IA1 14, IA2 10, IA3 14, IA4 8, TS2 11; mean 11.2, range
8–14. Team runs: 16, 13. The run-to-run spread of one agent is as large as the team–single gap.

**New statements beyond CS7:** 102371 (TW2) and 129365-c2 (IA). All solves across all runs are OEIS or one WOTW-II
statement. No Erdős, arXiv or paper statement was solved in any run.

**Conclusion of CS7–CS9:**
1. **Several agents beat one.** Teams and independent unions prove more statements than a single agent, and the single
   agent's set is (nearly) always a subset.
2. **The effect per run is small and noisy:** +2 to +6 statements. It is significant when pooled (p = 0.004; 0.06 under
   the strictest D8 sensitivity).
3. **The gain is explained by parallel attempts, not coordination.** Four independent copies match or exceed the
   coordinated team in coverage, and at equal tokens they are comparable. Expected union for k = 2 independent agents
   is already 14.3.
4. **Neither teams nor unions solve harder statements.**
