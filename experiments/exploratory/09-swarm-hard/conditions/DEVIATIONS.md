# CS5 protocol deviations and observed events (dated, append-only)

## E1 — 2026-10-12 ~00:00 +03: S2 orchestrator switched one worker to glm-5.2 after 429s (agent-initiated)
- In the launch burst, two S2 subagents (`ws_combi`, `ws_codes`) died with HTTP 429 ("Rate limit reached for
  requests"). The orchestrator respawned them.
- It respawned `ws_codes2` on `zai/glm-5.2` "so the rate limit is spread". z.ai accepted that model id, which our
  models.json does not declare.
- All other S2 and S3 GLM sessions use glm-5.3; S3 uses tensorfold/qwen3.8-flash-next for 2 workers so far.
- No written rule forbids it: AGENTS/TASK do not pin the model.
- Claude did not intervene. Messaging agents requires owner approval except for rule violations.
- **Paper:**
  - Report this as an emergent adaptation to provider limits.
  - Analyse S2's codes workstream (cwcode, bklc) with the model noted.
  - Next runs should pin allowed models in AGENTS.md.
- Rate-limit exposure at 00:45: S2 tmux 4 lines (429 at launch, with recoveries); S1 0; S3 0.

## E2 — 2026-10-12 00:26 +03: watchdog terminated an S2 foreground job
- `ws_auto` (depth 1) was blocked 22 min on `.venv/bin/python ws_auto/src/vdw_local...`. The watchdog terminated it
  as designed (rule announced in TASK.md).

## A1 — 2026-10-12 01:55 +03: keich-128 literature is newer than the HorizonMath baseline (analysis note)
- S1 submitted keich-128 = 0.10922515111460 at 00:53:11. The referee shows `beats_record=true` against the
  HorizonMath baseline 0.1148103258 (AlphaEvolve), a 4.86% improvement. Claude re-verified it independently:
  - quad-precision exact-crossing computation: 0.109225151114603
  - 400k-point grid with trapezoid rule: 0.109225151114003
  - intercepts in [-0.019, 0.203]
  - no network trace in the tmux history; the method is the agent's own (grid-midpoint surrogate + L-BFGS,
    60 restarts)
- **Newer literature:**
  - HorizonMath's own GPT result: 0.109148
  - Station (Chung, Du, Wesley, arXiv:2608.23691, Aug 2026; an open-world multi-agent system): about 0.107067 for
    n=128, as cited in search results; the normalization is not yet verified
- **Report as:** "beats the AlphaEvolve construction (the benchmark baseline), but not the best published AI
  results".
- **Before the paper:** check every instance's baseline against post-March-2026 literature. Station also reports
  604-point kissing configurations in dimension 11, which is not in our set.
- Station is directly related work: a multi-agent system with no equal-compute single-agent comparison.

## D3 — 2026-10-12 02:14 +03: harness fault killed the whole S3 condition; S3 resumed with the lost time added (Claude's error)
- **Cause.** The launcher's memory scope used systemd's default `OOMPolicy=stop`.
  - At 02:14:21 an S3 worker's `scripts/vdw_sat.py` reached 6.5 GiB anonymous memory and hit the scope's
    MemoryMax=10G.
  - The kernel OOM-killed that process (constraint MEMCG). systemd then **stopped the whole scope**: orchestrator,
    daemon, all subagents and the TensorFold clients.
  - The intent was to kill only the largest process.
- **Observed before the crash.** S3's orchestrator had been blocked for about 1.5 h in one tool call
  (`res = await h`, 3138 s and more) while its 6 subagents kept working. This is an orchestrator failure mode for the
  paper. The watchdog cannot see it, because no foreground child process exists.
- **Recovery, 02:47-02:52.**
  - **S1 and S2:** `OOMPolicy` cannot be changed at runtime. Their scopes were switched to MemoryHigh=10G (throttle,
    never kill) and MemoryMax=16G (backstop) with `set-property --runtime`.
  - **S3:** resumed from its root session with `prime-agent --resume` (47 messages of context), in a new scope with
    MemoryHigh=10G, MemoryMax=16G and OOMPolicy=continue, on the same cores 12-17. It received a factual system note:
    crash cause, not its fault, files intact, the new memory regime, and the new deadline.
  - **Lost time added:** 33 min (02:14:22 → 02:47). The S3 deadline moved from 07:46 to **08:19:28**, and
    `.budget_hours` became 8.55. S3 keeps 8 h of running time; its subagent team had to be rebuilt.
  - The old S3 supervisor and watchdog were stopped. New ones run with the new deadline.
  - The first relaunch attempt failed on shell quoting: apostrophes in the note inside single quotes. The second
    attempt used a wrapper script.
- **Analysis.** Report S3 as "resumed after harness crash". Its subagent state was lost. Its pre-crash solutions,
  ledger and files were intact.

## E3 — 2026-10-12 02:32-02:38 +03: S2 subagent read S1's workspace (cross-condition contamination of keich-128)
- **Evidence:** `_gates/isolation_scan.py` scans agent-authored tool inputs in the session files. S2's `ws_geom`
  subagent (sub-f336e01e), between 23:32 and 23:38 UTC:
  - listed `../S1/run`
  - tailed `../S1/run/keich/bh.log` and `../S1/run/heilb5.log`
  - read `../S1/scripts/keich_bh.py`, `keich.py` and `keich_fast.py`
  - read S1's ledger, solutions list and PROGRESS.md
  - copied `../S1/run/keich/bh_in.json` (S1's 0.109225 keich solution) to `ws_geom/sol/bhtest/` and verified it
  - logged this itself (ledger 02:45:26, agent ws_geom3): "method idea (grid-surrogate L-BFGS) re-implemented
    with my own code for S2"
- **Effect on S2 keich-128 = 0.10860102844 (03:02):**
  - Produced by `keich_lb.py 202 … WARM=ws_geom/sol/keich-128.json`.
  - Per the session log, that warm-start file then held S2's own 0.1146056 solution, so there was **no data copy**.
  - But the method was taken from S1 after reading its code, so this is **idea contamination**.
  - The S1/S2 intercepts correlate at 0.907.
  - **Paper:** exclude S2 keich from the comparison and report it as "derived after reading S1's code".
- **heilbronn-12:** S2 matched the record at 02:24, before the 02:32 access. Not affected. S2 read only S1's
  heilbronn log tail.
- **S1 and S3:** 0 agent-authored accesses to other workspaces. They see others' command lines in `ps` (same uid),
  which is a passive channel and not counted.
- **Root cause (Claude's):**
  - AGENTS.md said "Work only inside work/Sx/. Read ../../referee/ but never modify it, or anything else outside
    your workspace." The agent read this as "reading anywhere is allowed; modifying is not".
  - All conditions run as one Unix user, so the filesystem cannot isolate them.
- **Response 03:47-03:49:** an identical rule clarification went to every live session of all three conditions
  (launches.log): do not read, list, copy or use anything from other conditions; log any past access.
  `isolation_scan.py` is run every hour from now on.
- **Future runs:** separate Unix users or containers per condition, and explicit isolation wording.

## E4 — 2026-10-12 ~03:0x-03:2x +03: S2 froze under MemoryHigh throttling (consequence of D3), self-recovered
- **What happened:** S2's PROGRESS.md reports cgroup usage of 11.6 GB against a MemoryHigh of 10 GB. Every S2
  process was throttled to about 0.5% CPU.
  - The cause was ws_geom3's REPL kernel at 7 GB RSS.
  - Two urgent messages to that subagent got no reply for 15 min, so the orchestrator SIGKILLed the kernel. Memory
    fell to 1.98 GB and S2 recovered.
- **Interpretation:** a soft cap stalls the whole cgroup rather than one process, so it penalises S2 for the duration.
  The exact window is to be taken from the S2 logs.
- **Paper:** report this as a resource incident. The orchestrator diagnosed it and recovered on its own.

## E5 — 2026-10-12 04:52 +03: name-based process kills can cross conditions (same uid); agents' disclosures
- **Risk.** Agents use `pkill -f '<script>'`, and all conditions run as one user. Candidate cross-condition
  matches, by script basename present in the other workspace:
  - S1 at 01:01 ran `pkill -f 'heilbronn2.py'`; S3 also has a `heilbronn2.py`.
  - S3 at 03:46, 04:00 and 04:14 ran `pkill -f 'heilbronn2.py'`; S1 also has one.
  - S3 at 03:29 ran `pkill -f 'keich_opt.py --seed 101'`; S1 and S2 also have `keich_opt.py`.
  Whether a foreign process was actually running and killed at those times is to be reconstructed from logs in
  the final analysis.
- **Response 04:53.** An identical rule went to all live sessions: no pkill -f or killall; kill only your own PIDs.
- **Agent self-disclosures after the 03:49 isolation rule:**
  - **S3 orchestrator** (ledger 03:49:52): during crash recovery it read other conditions' process metadata (ps
    aux, readlink /proc/<pid>/cwd, taskset -cp on an S1 PID). A worker's ANALYSIS.md mentions "same finding as S1";
    the source is unclear.
  - **S2:** marked its keich solution as derived from S1's method (03:58).
  - **S2 ws_geom3:** "the 4 jobs I killed were mine; S1's jobs were not killed" (04:01).
  - **S1:** none needed (0 accesses).
- **Isolation scan 03:42-04:52.** The only hits are compliance declarations that quote the paths. No new file
  access.
- S2 watchdog: session ws_codes3 blocked over 55 min. The targeted PID is a zombie (empty cmdline), so SIGKILL has no
  effect; this is log noise only.

## A2 — 2026-10-12 04:55 +03: S1 keich-128 = 0.10819492762339 (independent, verified)
- S1 submitted 04:49:29; ledger: "seed-2 restart sweep, grid-midpoint surrogate L-BFGS".
- **Re-verification:**
  - quad-precision exact-crossing: 0.108194927623389
  - 400k-point grid: 0.108194927623084
  - intercepts in [-0.295, -0.086]
- **Provenance:** S1 shows no network trace, and the isolation scan shows 0 accesses to other conditions.
- **Literature (A1):**
  - beats AlphaEvolve 0.1148103 by 5.76%
  - beats HorizonMath's GPT result 0.109148
  - does not beat Station (arXiv:2608.23691), about 0.107067; its normalization is still to be verified
- **For the paper:** the best clean keich result of CS5 came from the single agent.

## E6 — 2026-10-12 06:55 +03: network-source violations (TASK.md allows literature only via arXiv/OpenAlex/Crossref)
Agent-authored HTTP requests by domain, from all session files, subagents included:
- **S1:** none.
- **S2:**
  - en.wikipedia.org `/wiki/Sparse_ruler` (00:19 local)
  - ljcr.dmgordon.org `/cover.html` (00:52; La Jolla index page)
  - www.combinatorics.org: 5 requests (02:37; journal article pages)
  - doi.org: 1
  - (the www.w3.org hit is an XML namespace string, not a request)
- **S3:** www.codetables.de / codetables.de, 12 requests (05:54 and 06:21), including `BKLC.php?q=2&n=68&k=15`,
  Grassl's construction page for exactly this instance.

Per-instance consequences:
- **S3 bklc-68-15 d=24 (06:00 lead-code3, 06:30 lead-code2): VOID for the capability comparison.** It reimplements
  the Grassl table's construction, fetched from a forbidden source for this exact instance. The orchestrator itself
  labelled it "record MATCH via faithful reimplementation of a published construction, NOT a novel construction".
  S3's clean bklc best before the access was d=22.
- **S2 covering-13-7-4 = 30 (00:11, CP-SAT): clean.** It predates the LJCR access (00:52). No better cover was
  submitted.
- **S2 ruler-10000:**
  - 177 (00:36) and 174 (03:34, generalized Wichmann scan) came after the Wikipedia Sparse_ruler access (00:19).
  - The Wichmann construction is textbook knowledge, so flag these as "possibly informed by a non-allowed source"
    and report them separately.
- The S2 combinatorics.org access (02:37) concerned journal articles. Treat it as literature reading outside the
  allowed APIs: flag it, no instance attributed yet.

**Response:** at 06:55 an identical reminder went to all live sessions of all three conditions.

**Lesson for future runs:** enforce the network allow-list technically, with a per-condition proxy or a netns
firewall; written rules are not enough for swarms.

## E7 — 2026-10-12 ~09:05 +03: S3's final bklc-68-15 d=24 is a clean own construction (verified)
- At 08:09 S3 replaced 22 with a d=24 code that it reports came from an exhaustive enumeration of all binary cyclic
  codes of length 63 (`leads/lead-code3/scripts/cyclic_enum.py`, created 05:48:55; `logs/cyc63.log`, born 05:49:42,
  DONE 05:54:32, listing 12 [63,15,24] cyclic codes).
- **Claude's checks:**
  - file birth and modification times
  - the session transcript: the first codetables HTTP GET is at 05:54:48 local, after the enumeration finished
  - the submitted matrix:
    - the first 5 columns are zero
    - the last 63 columns span a cyclic code (shift-closed), rank 15
    - the generator polynomial has degree 48
  - referee: d=24
- **Verdict:** a clean record match by the agent's own search.
- **Caveat:** between 05:29 and 05:39 the same agent's reasoning planned to "websearch for an explicit [68,15,24]
  generator matrix". That shows intent against the rule's spirit. Report it as a behavioural finding.
