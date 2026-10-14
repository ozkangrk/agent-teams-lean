# CS5 evaluations (Claude, 2026-10-12 ~09:00 +03)

Final verdicts: `work/Sx/final_verdict.json`. Gates: `work/Sx/final_gate.txt`, where S1, S2 and S3 all show
[PASS] cs5 gate / [PASS] cs5 gate / [PASS] cs5 gate. Isolation scan: `conditions/final_isolation_scan.txt`. Tokens:
`conditions/token_account.json` (all session files, subagents included, recursive).

| Instance | Best known | S1 single agent | S2 swarm ≤4 GLM | S3 hybrid ≤12 (8 GLM + 4 local Qwen) |
|---|---|---|---|---|
| keich-128 | 0.1148103258186177 | 0.1081949228 (-5.8e-02) ★beats | 0.1074567273 (-6.4e-02) ★beats [contaminated (E3: method taken from S1)] | 0.1099301969 (-4.3e-02) ★beats |
| heilbronn-12 | 0.0325988586918197 | 0.03259885869 (+7.2e-12) ✓match | 0.03259885869 (+7.2e-13) ✓match | 0.0308298027 (+5.4e-02) |
| tammes-15 | 53.65785012993267 | 53.65785013 (-1.3e-16) ✓match | 53.65785013 (+1.9e-15) ✓match | 53.60149471 (+1.1e-03) |
| autocorr-c1 | 1.5028503020710076 | 2 (+3.3e-01) | 1.50842766 (+3.7e-03) | 1.512086896 (+6.1e-03) |
| dts-7-5 | 112 | — | 130 (+1.6e-01) | 123 (+9.8e-02) |
| vdw-2-7 | 3703 | — | 3703 (+0.0e+00) ✓match | 608 (+8.4e-01) |
| cwcode-29-8-5 | 36 | — | 28 (+2.2e-01) | 35 (+2.8e-02) |
| covering-13-7-4 | 30 | 30 (+0.0e+00) ✓match | 30 (+0.0e+00) ✓match | 30 (+0.0e+00) ✓match |
| bklc-68-15 | 24 | — | 22 (+8.3e-02) | 24 (+0.0e+00) ✓match |
| ruler-10000 | 174 | — | 174 (+0.0e+00) ✓match [flagged (E6: Wikipedia accessed before)] | 192 (+1.0e-01) |

## Clean comparison
E3 contamination and E6 sources are excluded; D3 means S3 was resumed after a harness crash with the lost time added.
- **Valid solutions:** S1 4/10, S2 10/10, S3 10/10. The 4-agent swarm covers everything, while the single agent
  went deep on a few instances.
- **Records matched or beaten:**
  - S1: 4 (keich beats, heilbronn, tammes, covering)
  - S2: 4 clean (heilbronn, tammes, vdw 3703, covering), plus ruler 174 (flagged) and keich (contaminated)
  - S3: 3 (keich beats, covering, bklc d=24 from its own cyclic-code enumeration; see E7)
- **keich-128 (continuous, AI-held record):**
  - The best clean result is **S1's 0.1081949228** (final file; 0.10819492762 was verified independently at
    04:55, A2). It was independently re-verified (A2). It beats AlphaEvolve
    0.11481 and HorizonMath's GPT 0.109148, but not Station's ≈0.107067.
  - S2 reached 0.10745673 after reading S1's code (E3), so it is excluded.
  - S3 reached 0.10993020.
- **Best per remaining instance:**
  - autocorr: S2 1.50842766 (gap +3.7e-3)
  - dts-7-5: S3 123
  - vdw-2-7: S2 3703 (match)
  - cwcode-29-8-5: S3 35, with an original Z7-symmetric construction; the record is 36
  - bklc-68-15: S3 has 24 (record match) from an exhaustive enumeration of length-63 cyclic codes, padded with 5
    zero columns. It finished at 05:54:32, before the first codetables GET at 05:54:48. The Grassl-recipe 24 (E6)
    was quarantined. See E7. S2 has 22.
  - ruler-10000: S2 174 (flagged)
- **No clean result beats an open (group B) record.**

## Cost (GLM tokens; the local Qwen costs no provider quota)
- S1: 341 calls, 21.9M input (incl. cache reads), 0.24M output
- S2: 1257 calls, 69.5M input (incl. cache reads), 1.12M output; 124 of its calls ran on glm-5.2 (E1)
- S3: 1722 calls, 86.8M input (incl. cache reads), 1.67M output; local Qwen 321 calls / 0.42M output

## Local Qwen contribution (S3)
- **Agents:** 4 Qwen3.8 subagents: 2 ruler workers (lead-combB-ruler and ruler2), 1 local-search worker (w2-ls) and 1
  monitor (q-mon).
- **Workload:** about 19% of S3's model calls and about 25% of its output tokens.
- **Results:**
  - No record-level result is attributable to them.
  - S3's ruler best stayed at 192.
  - The monitor role verified scorer outputs.

## Process findings (see DEVIATIONS.md)
- D3: harness OOM policy stopped S3 completely; it was resumed.
- E1: an agent switched itself to glm-5.2 after 429s.
- E3: cross-condition reading (S2 read S1's files).
- E4: a soft memory cap froze S2; it recovered on its own.
- E5: name-based kill risk.
- E6: forbidden web sources (S2, S3).
- The S3 orchestrator was blocked for about 1.5 h in one `await` before the crash.
- **Rule compliance by condition:**
  - S1: 0 violations
  - S2: cross-condition reading, plus web sources
  - S3: web source, plus process-metadata peeking during recovery
