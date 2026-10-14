# CS4 evaluations (Claude, 2026-10-11 23:50 +03)

Final verdicts: `work/S1/final_verdict.json`, `work/S2/final_verdict.json` (referee unchanged during the run).
Gate outputs: `work/Sx/final_gate.txt`.

| Instance | S1 single agent | S2 swarm (≤4) |
|---|---|---|
| thomson-282 | 37159.05162 (+3.2e-04) | 37147.29442 (+1.0e-14) ✓ |
| thomson-400 | 75605.71504 (+3.1e-04) | 75582.44851 (+1.5e-15) ✓ |
| thomson-470 | 104850.5372 (+2.6e-04) | 104822.9232 (+3.5e-07) |
| circles-26 | 2.635983069 (-1.2e-06) ✓ | 2.635983082 (-1.2e-06) ✓ |
| circles-32 | 2.939572752 (-1.9e-04) ✓ | 2.939572469 (-1.9e-04) ✓ |
| autocorr-c1 | 1.512170216 (+6.2e-03) | 1.504769007 (+1.3e-03) |
| discrepancy-2 | 1160 (+0.0e+00) ✓ | 1160 (+0.0e+00) ✓ |

Notes:
- **autocorr-c1.** The gap is against the true state of the art, 1.5028503 (A3), not records.json.
- **circles.** The "beats" are against truncated published values. Report them as matched to printed precision (A1).
- **Records matched.** S2 matched 5 of 7 instances (thomson-282, thomson-400, circles-26, circles-32,
  discrepancy-2); S1 matched 3 of 7 (circles-26, circles-32, discrepancy-2).
- **Remaining instances, where S2 is closer:**
  - thomson-470: S2 gap 3.5e-7; S1 gap 2.6e-4, about 750 times larger.
  - autocorr: S2 gap 1.28e-3; S1 gap 6.2e-3, about 5 times larger.
  - S2's autocorr 1.50477 is below AlphaEvolve v1's 1.5053.
- **Ledger.**
  - S1 has 22 lines.
  - S2 has 179 lines, 115 of them by its autocorr subagent at the 22:50 check.
- **Time to all 7 valid solutions.** S2 took 33 min; S1 took 99 min, including the 38-min blocking-call stall (D1).
- **Gates.**
  - S2: PASS.
  - S1: FAIL on format only.
    - RESULT.md claims are dicts instead of plain numbers, and one key is `edp-discrepancy2`.
    - The scores inside the dicts are consistent with the referee: True.
  - Asymmetry: S2 received gate output in a supervisor nudge at 22:39 and fixed its format; S1 was never idle, so it
    never received gate feedback.
  - Same pattern as CS3 C2: the autonomous gate loop is inactive in the TUI.
- **Deviations and notes:** D1 (watchdog), D2 (single-threaded BLAS), E1 (gate crash on a non-numeric claim), and
  A1-A3 (record values) in DEVIATIONS.md.
