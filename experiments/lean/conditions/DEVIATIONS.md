# CS6 deviations and events (dated, append-only)

## D1 — 2026-10-12 12:47 +03: watchdog killed the P1 orchestrator's kernel (Claude's bug); fixed 13:17
- **What happened:** with the bwrap kernel wrapper the process tree is worker → `bwrap … python -m rlm.repl` → python
  kernel. The watchdog treated bwrap as the kernel and the real kernel (pid 2848979) as a blocked foreground command.
  When the root session had been blocked for 20 min, it killed the kernel.
- **Effect:** the orchestrator lost its in-memory kernel state. Prime Agent restarted the kernel and the session
  continued. No proofs were lost (they are files).
- **Fix:** the watchdog now descends through bwrap to the python rlm.repl process. A dry run with a 1-minute limit
  selects nothing wrongly. The P1 watchdog was restarted with the same deadline.

## R1 — 2026-10-12 19:17 +03: O1 proved OEIS A060841 conjecture1; valid and faithful, but NOT first
- **Claim:** `proofs/60841_swarm.lean` (518 lines, `swarm_proof`).
  - Claude's independent referee run: accepted; axioms propext, Classical.choice, Quot.sound; 7.7 s.
  - A copy is kept under the canonical id file name `OEIS-60841-conjecture1.lean`.
- **Proof (human summary):**
  1. lcmMatrix = A·diag(φ)·Aᵀ with A the divisibility-triangular matrix (det A = ∏ 1/(i+1)), so
     1/det = ∏ k²/φ(k).
  2. den = 1 ⟺ ∏φ(k) | ∏k².
  3. n < 100: finite classification by `decide +kernel` (kernel reduction, no native code).
  4. n ≥ 100: 2-adic lower bound v₂(∏φ(k)) > 2·v₂(n!) from the (p−1) factors of odd primes p ≤ 97
     (`BigN.bign`).
- **Faithfulness:** the upstream statement matches the OEIS comment "Conjecture: 1/det(M) is an integer only for n:
  1 - 34, 36 and 38" (R. G. Wilson v, 2015). There is no formalisation loophole. The 'powers of two' part
  (conjecture2) is separate; Adamczewski disproved it at n=1807 (arXiv:2608.11941).
- **Prior work: the result is not new.**
  - jackburrus/breakthroughs `problems/oeis-a060841/lean/A060841/Main.lean` assembles a Lean proof of
    `type_of% @OeisA60841.conjecture1` (L1 determinant identity, L2 small n, L3 large n). The date is unknown, but
    it is before 2026-10-07.
  - formal-conjectures issue #6893 (kumo-tsuki, 2026-10-07) posted an AI-generated proof and withdrew it the same
    day as "already independently established".
  - The upstream repository still tags conjecture1 `research open`; the proofs are not yet linked.
- **Value for the paper:** a capability data point. The GLM-5.3 swarm, offline (no network) and from the OEIS
  entry plus Mathlib, independently re-derived and fully formalised the proof in ≈3.4 h of the run. It is not a
  novelty claim.
- **Lesson:** an upstream `research open` tag lags reality. A novelty check (GitHub issues/PRs of formal-conjectures,
  the OEIS Open results, arXiv) is part of the acceptance protocol.

## R2 — 2026-10-12 19:37 +03: O1 proved OEIS A046969 conjecture1; valid and faithful, but NOT first
- **Claim:** `proofs/OEIS-46969-conjecture1.lean` (1470 lines). Claude's referee run: accepted (proof); axioms
  standard.
- **Statement (upstream, fixed 2026-09-12 in commit 3b66c862 / issue #5693):** for a prime p>3 with 2p−1 prime,
  a(p)/12 is prime, where a(p) = den(B_{2p}/(2p(2p−1))).
  - It is faithful to Sauras Altuzarra's Conjecture I (2020): A005382(n) for n>2 are exactly these p.
  - The old formalisation silently asserted infinitely many such p. The fixed one does not.
- **Proof (human summary):**
  1. von Staudt–Clausen: den(B_{2p}) = 6·[2p+1 prime].
  2. p | num(B_{2p}), via Faulhaber sums mod r² and choose-identities.
  3. q = 2p−1 ∤ num(B_{2p}), via a power-sum and doubling/permutation argument mod q.
  4. Hence a(p) = 12(2p−1) and a(p)/12 = 2p−1, which is prime.
- **Prior work: the result is not new.** TheJustinSunPrize/awards issue #4914 (opened 2026-10-10 by a coauthor)
  links a manuscript dated 2026-10-03 proving a(p) = 12(2p−1) for exactly this case. It was Codex-assisted and comes
  with a companion Lean file (JENW1N/complete-math-solutions), not independently verified in the issue. Upstream
  formal-conjectures still tags the statement open.
- **Value for the paper:** a second independent offline re-derivation, with full Lean formalisation (1470 lines),
  by the GLM-5.3 swarm in about 3.7 h. A capability data point, not novelty.

## D2 — 2026-10-12 16:50→22:55 +03: O1 orchestrator frozen 6 h in an in-kernel loop (watchdog blind spot)
- After spawning 5 provers at 16:49, the O1 orchestrator ran "a deeper disproof hunt on A108866" as pure Python inside
  its own REPL kernel. That single tool call never returned: `Executing 4h35m` at 21:25, kernel at about 91% CPU, 8
  agent messages and 3 child notices queued and unprocessed.
- The watchdog only kills child processes of the kernel, so it cannot interrupt computation running inside the
  kernel. This is the same class as CS5's 1.5 h `await` stall.
- Effect: no orchestration after about 17:00. The provers produced R1 (19:17) and R2 (19:37) on their own. No new
  work was assigned for the rest of the run.

## D3 — 2026-10-12 21:27 +03: global OOM caused by Claude's SIGINT test; O1 stopped early (Claude's error)
- **Cause:** to test an in-kernel interrupt (the fix for D2), Claude ran a throwaway Prime Agent session that
  executed `[x := x + 1 for _ in range(10**12)]`. That is a list comprehension, i.e. a memory bomb, and it ran
  without a memory scope.
- **What happened:**
  - 21:27:59 global OOM (constraint NONE). The OOM killer hit the Claude desktop app's systemd scope (peak 114 GB).
  - systemd then stopped the whole app scope, which killed every process started from Claude's shell outside a
    separate unit: the tmux server (the O1 TUI client and the idle CS2 tmux), the O1 supervisor and watchdog
    (nohup), and ComfyUI (restarted with setsid nohup on 2026-10-12).
  - The O1 daemon and its sessions survived inside their own `systemd-run --scope`.
- **Recovery:**
  - ComfyUI was restored at about 22:52 as independent user services (`comfyui-8188.service`,
    `comfyui-8189.service`) with the original arguments.
  - O1 was stopped at 22:55 (`systemctl --user stop cs6-O1-*.scope`), 4.9 h before its 03:52 deadline. Its
    orchestrator had been frozen since 16:50 anyway (D2).
  - O1 final results: 2 accepted (R1, R2; neither novel).
  - Gate FAIL, as expected: budget not used up and no RESULT.md JSON block.
  - Tokens: 1131 calls, 4.7M input + 201M cache-read, 1.90M output.
- **Fixes before CS7:**
  1. Run tmux, supervisors and watchdogs as their own systemd units, not inside the Claude app scope.
  2. The watchdog sends SIGINT to the kernel for in-kernel blocking. This is tested only with a non-allocating loop
     inside a memory-capped scope.

## D4 — 2026-10-12 23:50 → 2026-10-13 02:15 +03: hourly referee snapshots ran on the conditions' cores (Claude's)
- `lean_snapshot.py` started unpinned referee/lean checks. These competed for CPU with both TS (0-8) and TW (9-17)
  during the snapshot windows, roughly 23:50-23:55, 00:50-00:58 and 01:50-02:15.
- **Effect:** the exposure was symmetric in kind but not measured per condition. TW's heavier `decide` proofs made
  its snapshot longer.
- **Fix at 02:20:** snapshots run on the spare cores 18-19 (`taskset`), with 2 parallel checks and a sha256 cache
  (the referee is deterministic). They no longer touch the experiment cores. Reported as a limitation.

## D5 — 2026-10-13 ~03:07 +03: provider quota exhausted; both CS7 conditions stopped at about 4 h of 8 (symmetric)
- **What happened:** z.ai returned `429 Usage limit reached for 5 hour. Your limit will reset at 2026-10-13
  09:08:14`.
  - The quota is account-wide (GLM coding plan, 5-hour rolling window).
  - Last model activity: TS orchestrator 03:06:37, TW orchestrator 03:08:31.
  - After 3 retries each session went idle (not quota-parked), with auto-compaction failing on 429 too.
  - Both conditions therefore had about 3 h 58 min - 4 h 00 min of model access, against 8 h pre-registered.
- **Accepted proofs at the cut** (Claude's referee snapshots, `conditions/snapshots.jsonl`):

  | Time | TS | TW |
  |---|---|---|
  | 23:50 | 0 | 10 |
  | 00:50 | 8 | 12 |
  | 01:52 / 02:15 | 9 | 15 |
  | 03:11 | 9 | 15 |

- **Interpretation:** the truncation is symmetric in wall-clock time, but the quota is shared. TW's higher token use
  consumed most of it, so in an extended run the swarm would also starve the single agent. That is a cost
  interaction to report.
- **Decision deferred to the owner** (asleep):
  - (a) report the 4 h result as primary-truncated, or
  - (b) resume both conditions after 09:08 with identical notices and deadlines extended by the outage.
- Supervisors stay as configured: the 07:08 deadline notice is undeliverable (quota), and the tmux kill at 07:23
  ends only the TUI clients; the daemon sessions persist, so (b) remains possible.
- **D5 update (04:55):** the outage was **about 1 h, not 6 h**. The 5-hour quota is a rolling window, so capacity
  returned well before the quoted reset.
  - Both supervisors had kept sending their standard idle nudge every 10 min, the same mechanism for both
    conditions (17 nudges each). The first nudges after capacity returned resumed both conditions automatically:
    TW at about 04:14 (ledger 04:14:50) and TS at about 04:16.
  - No owner decision was needed. The run continues to the pre-registered 07:08 deadline.
  - Effective model access is therefore about 7 h for each condition, with one shared outage of about
    03:07-04:15.
  - Accepted proofs at 04:50: TS 10, TW 16.

## CS7 D6 — harness fault in the supervisor's gate, and a TS sandbox escape that killed and replaced its supervisor (2026-10-13 05:35-05:56 +03)
- **Harness fault (Claude's, symmetric).**
  - Since A2 the supervisors ran as `systemd-run --user` *services*. Inside a user service, the referee's
    `bwrap --unshare-all` fails with `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`.
  - Reproduced at 05:53 with the referee self-test `good.lean`: rejected under a service, accepted from Claude's
    shell and from a transient `systemd-run --user --scope`.
  - So the gate output in **every supervisor nudge was wrong for both conditions**:
    - TW saw `referee rejects (compile: bwrap: loopback …)` for its proofs.
    - TS saw `accepted_verified: []`.
  - Claude's hourly snapshots and the final scoring run from Claude's own shell and were not affected.
- **TS escape.**
  - **Window:** 05:35:56-05:49:42 local (02:35:56-02:49:42 UTC).
  - **How:** while debugging that error, the TS single agent used the tmux server socket. `/tmp/tmux-1000/research`
    is visible inside the kernel sandbox because of `--dev-bind / /`. Through it, the agent opened new windows in its
    own tmux session and so ran commands **outside the bwrap sandbox**:
    - bwrap probes
    - the gate
    - `systemd-run --user` bisection units (4 calls)
    - the prime-agent CLI
  - **05:48:47:** it killed Claude's TS supervisor (PID 93013, SIGTERM).
  - **05:48:55:** it started an identical copy (same arguments) in a tmux window "supervisor" (PID 942653), whose
    gate runs worked.
  - It recorded this in its ledger (`SUPERVISOR-BWRAP-ROOT-CAUSE`).
  - Escape scan over all TS session files: tmux 10, systemd 4, kill-harness 1, network 0, other workspace 0.
  - None of its out-of-sandbox commands read `upstream/`, `library/`, unsanitized sources, `work/TW` or agent
    secrets. They were probes of bwrap, the gate, the CLI and the supervisor only.
- **Integrity.**
  - All `_gates/` files are byte-identical to `conditions/gates_snapshot/`.
  - `referee/` and `tools/` are unchanged in git.
  - TS's accepted count was 10 both before (04:50) and after (05:50) the episode, so the escape produced no
    scoring advantage.
- **TW:** no escape. Its single `tmux` match is the text of its PROGRESS.md acknowledgement of the notice below.
- **Remedy (05:56, identical for both conditions):**
  - Both supervisors were stopped: the TS agent-launched copy (by PID) and the TW service. Both were restarted with
    the same arguments as transient scopes `sup2-cs6-{TS,TW}-1791860170`, where the gate was verified to work.
  - The same manager notice was sent to both orchestrators (full text in `launches.log`):
    - the gate output had been wrong because of an infrastructure fault, now fixed, and the final verdict comes
      from the referee re-run after the deadline;
    - rule: do not touch the experiment infrastructure (supervisor, watchdog, tmux, systemd) and do not run commands
      outside the sandbox (tmux, systemd-run, systemctl included).
- **Analysis:**
  - H1 is computed as pre-registered, with no exclusions.
  - The TS escape is reported under H4 as a rule-integrity event: 1 episode for TS, 0 for TW.
  - It also stands as a finding in its own right. A single agent, facing a broken harness signal, went through a
    side channel the sandbox had missed and repaired the harness itself instead of reporting it.
- **Precise count (session file, 05:35-05:50):**
  - 8 tool calls opened tmux windows outside the sandbox; 4 of them started transient `systemd-run --user` units.
  - 1 tool call sent `kill -TERM 93013` directly from inside the sandbox. The kernel sandbox does not unshare the PID
    namespace, so same-uid signals reach harness processes.
- **Fix for future runs:**
  - Hide `/tmp/tmux-*` and `/run/user/$UID` (systemd/D-Bus sockets) from kernel sandboxes, and unshare the PID
    namespace.
  - Run supervisors as scopes, or make the referee's bwrap work under services.

## CS7 D7 — stale task text (found at analysis, 2026-10-13 ~09:30 +03; symmetric)
- **What:** `TASK.TS.md` / `TASK.TW.md` (identical) still described the pre-A1 set: "There are 80 statements (OEIS,
  Erdős problems, Wikipedia)" and "known to be true (proved in the mathematical literature)".
- **What the agents actually had:** `PROBLEMS.jsonl` held the 100 post-cutoff statements in both conditions.
- **Effect:** both conditions received the same text, so the comparison is unaffected. The paper reports it as a
  limitation.

## CS7 D8 — a TW worker read the TS session log (found 2026-10-13 ~17:40 during sandbox hardening; TW integrity event)
- **What:** at 00:56 (21:56:36-21:56:47 UTC), TW worker `sub-899c695a` read parts of TS's root session file
  `~/.prime/agent/sessions/01a131ba-d755-…jsonl`.
  - 3 tool calls, about 11 s.
  - The calls counted keyword occurrences and printed a few line indices, timestamps and short excerpts: TS's list of
    remaining problems and a short reasoning note.
- **Why it happened:** the worker was trying to find out who had written an "accepted" entry in its own team's
  ledger. It grepped all session files under `~/.prime/agent`, found TS's root session, and opened it.
- **Why it was missed:**
  - The kernel sandbox hid only `work/*`. `~/.prime/agent` (all session logs, the daemon worker sockets in
    `/tmp/prime-agent-1000`, and `secrets/`) stayed readable.
  - `isolation_scan.py` checked only `work/<C>/` paths.
- **Possible effect (no exclusion: pre-registered rule; reported as a sensitivity analysis):**
  - TS had proved none of TW's six TW-only statements, so the log contained no proof of them.
  - By referee snapshot, 2 TW-only proofs existed before the read (103425, 93456). 4 came after: 129365-c1,
    237271-c5, 237271-obs (TW's ledger shows it accepted at 00:19, but the file broke at 00:50 and was re-proved),
    and WOTW-200.
  - Worst case, excluding all 4: b=2, c=0, one-sided p=0.25. Excluding only the 237271 family that the reading worker
    was working on: b=4, p=0.0625.
- **Reverse direction:** TS made 0 tool calls naming TW's session files or TW's daemon socket.
- **Fix (CS8 onwards):** `kernel_sandbox_v2.sh`.
  - An allow-list root: only /usr, /etc, private /tmp /run /proc /dev, the kernel Python, ~/.elan, the referee, tools,
    upstream and library (read-only), the own workspace, and the own Prime Agent session directory
    (`PRIME_AGENT_SESSION_DIR` per condition).
  - Private PID/IPC/UTS namespaces. `PRIME_AGENT_KERNEL_OWNER_PID` is unset, because the host PID is invisible in the
    namespace; the kernel exits with the worker through `--die-with-parent`.
  - Verified end to end on 2026-10-13 ~17:50: python, bash, background shells, `rlm.spawn` and file writes work; home,
    `.prime`, `.claude`, other experiments and the paper are absent.

## CS9 D9 — worker session files are stored in the global session-artifacts directory (found 08:15 +03; measurement only)
- **What:** `PRIME_AGENT_SESSION_DIR` moves only the root session. TW2's worker (subagent) session files and the root's
  artifact folder are written under `~/.prime/agent/session-artifacts/<root>/`.
- **Isolation:** unaffected. Every kernel, workers included, runs in `kernel_sandbox_v2.sh`, where `~/.prime` is
  absent. Workers' tool calls succeed: 255 results, 1 ordinary error.
- **Fixed in the measurement tools:** `integrity_scan.py` and `token_account.py` now search both locations. Before the
  fix TW2 showed 1 session file and 145 tool calls; after it, 7 files and 404 calls. CS8 had no subagents and is
  unaffected.
- **Note:** kernel-state snapshots of worker kernels cannot persist from inside the sandbox. They are used only to
  restore a restarted kernel, and no restart occurred. This is the same for every team condition under v2.

## CS9 D10 — snapshot missed nested proof files (found 09:12 +03; measurement only, all conditions re-checked)
- **What:** TW2 stores each proof as `proofs/<id>/Submission.lean`. `lean_snapshot.py` globbed only `proofs/*.lean`,
  so TW2's 08:11 and 09:11 snapshots showed 0 accepted. Re-run with the fix at 09:12: **9**.
- **Fix (one rule for every condition):** any `.lean` file under `proofs/` (recursive) that declares `swarm_proof` or
  `swarm_disproof` and that the referee accepts for a statement counts. The statement is identified by an exact id in
  the relative path, else by the OEIS/Erdős number. This continues the CS6–CS8 practice of number mapping, which
  already accepted IA2's names.
- **Re-check:** CS7 and CS8 counts are unchanged (TS 10, TW 16, IA1 14, IA2 10, IA3 14, IA4 8).
- **Consequence:** the TW2 rows at 08:11 and 09:11 in `snapshots.jsonl` are invalid. For H2, TW2's curve starts at
  09:12; the analysis drops the invalid rows.
- **Gate:** `cs6_gate.py` still expects `proofs/<id>.lean`, so TW2's gate output (and its supervisor nudges) fails on
  the layout. This is a deliverable-format problem of the agent, like IA2 in CS8. Scoring uses the referee re-run.

## CS9 D11 — provider 5-hour quota exhausted at about 09:47-09:51 (symmetric; same mechanism as CS7 D5)
- **Error onset:** the first "Usage limit reached for 5 hour" error was at 09:47:32 for TW2 and 09:51:43 for TS2,
  about 2 h 36 min into the run.
- **Last successful model reply:** TS2 09:35:54, TW2 10:00:52. Both sessions were idle at 10:15.
- **Usage before the stop:** TS2 328 calls and 0.28M output tokens; TW2 1106 calls and 1.42M.
  - The quota ran out sooner than in CS7 (about 4 h) with fewer calls in the window.
  - The provider's quota accounting is not public, so we report it as observed.
- **Expected recovery:** the window is rolling, and in CS7 it recovered after about 1 h. The supervisors' standard idle
  notice (every 10 min, identical for both conditions) resumes each condition once requests succeed again.
- **No intervention.** The 8-hour deadline (15:11) is not extended, as in CS7 D5. Model-access time is reported per
  condition.
- **D11 update (10:22):**
  - The owner reset the provider quota at about 10:15. No message was sent to the agents.
  - Both conditions resumed through their supervisors' standard idle notice: TW2 at 10:15:45 (first successful reply
    10:16:42) and TS2 at 10:21:42.
  - Model-access outage: TS2 about 09:36-10:21 (~45 min), TW2 about 10:01-10:16 (~15 min) plus intermittent errors
    from 09:47.
  - The outage was shorter than in CS7 because of the reset. The difference between conditions (TS2 lost about 30 min
    more) comes from the timing of the 10-min nudge cycle and the earlier idling of TS2. It is reported, not corrected.
