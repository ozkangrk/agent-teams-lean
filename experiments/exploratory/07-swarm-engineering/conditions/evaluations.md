# CS3 evaluations (Claude)

## C1: single agent (launched 09:21; agent declared completion ≈11:50, i.e. ≈2.5 h of the 6 h cap)
- **Claim** (RESULT.md): HEAD d11745f6, 98.26 tok/s, ×1.036 decode.
- **Gate** (`cs3_gate.py`, re-judged by the referee): PASS. Correct, 24/24 identical, 0 near-tie flips; claim within tolerance.
- **Hidden set** (14 prompts never shown): correct, 14/14 identical. Decode 99.05 vs. baseline 95.83 in the same session
  → **×1.034**.
- **Ledger:** 10 attempts (5 self/suite-local checks, 1 referee-rejected attempt: glue-v1 incorrect, then fixed to
  bit-exact; 1 final). Dead ends: the direct global router read (−3%), route-before-fork (−3.4%), the COLS=16 shared
  kernel (bit-exact but slower).
- **Notes:** autonomous gate inactive in the TUI (see ARCHITECTURE.md); the agent rewrote its ledger once
  (`rm -f` + rewrite, contents intact).

## C2: swarm (launched 13:11; agent declared completion ≈16:10, i.e. ≈3 h of the 6 h cap)
- **Structure:** orchestrator + 3 engineers (eng-glue, eng-gemv, eng-moe) in parallel branches, then integration with
  end-to-end A/B. Regressions were reverted (gemv per-shape, moe experts16: kernel-level wins, −1.0…−1.5% end to end).
- **Claim** (RESULT.md, prose; **no JSON block**, so `cs3_gate.py` FAILED on format before judging): "≈1.05×
  (100.3–100.6 tok/s)" at HEAD 7040fce7.
- **Referee** (clean GPU, integrity guard active): C2-final2 correct, 24/24 identical, 100.48 tok/s, **×1.0588**. The
  claim is conservative and consistent.
- **Hidden set** (14 prompts): correct, 14/14 identical. 99.87 vs. baseline 95.59 → **×1.045** (C1: ×1.034).
- **Verdict count:** 18 referee verdicts in total (C1: 3), including 3 incorrect/failed (caught) and 3
  anomaly-affected (ComfyUI renders 15:52–15:57; see the referee guard commit).
- **Ledger:** 15 lines. Some subagent attempts appear only in `verdicts/`.
- **Process events:** a third-party GPU load disturbed the A/B runs; the orchestrator detected it and paused, the
  referee guard was added, and ComfyUI was stopped with the owner's permission. The gate never ran during the
  condition (autonomous loop inactive in the TUI), so the format violation was not surfaced to the agents.

## CS3 summary (C1 vs C2, same task, same model, same referee)
| | C1 single | C2 swarm |
|---|---|---|
| verified decode speedup (visible suite) | ×1.036 | ×1.0588 |
| hidden-set speedup | ×1.034 | ×1.045 |
| wall clock to completion | ≈2.5 h | ≈3.0 h |
| referee verdicts | 3 | 18 |
| correct, kept improvements | 3 kernel changes | prefetch + PDL on glue kernels (others tried and rejected end to end) |
