# RESULT.md — CS9 condition TW2 (swarm)

Working directory: `work/TW2`. Budget 07:11–15:11. Ledger: `ledger.jsonl` (append-only, every referee run logged).

## Accepted (referee-verified) proofs

```json
{
 "accepted": [
  "OEIS-100434-conjecture2",
  "OEIS-100434-conjecture3",
  "OEIS-102371-conjecture",
  "OEIS-103425-conjecture",
  "OEIS-108306-conjecture",
  "OEIS-112970-conjecture1",
  "OEIS-112970-conjecture2",
  "OEIS-113250-conjecture",
  "OEIS-113252-conjecture",
  "OEIS-113255-conjecture",
  "OEIS-237271-observation_carmichael",
  "OEIS-3625-conjecture"
 ]
}
```

- ACCEPTED OEIS-100434-conjecture2 (see `proofs/OEIS-100434-conjecture2/Submission.lean`, ledger entry)
- ACCEPTED OEIS-100434-conjecture3 (see `proofs/OEIS-100434-conjecture3/Submission.lean`, ledger entry)
- ACCEPTED OEIS-102371-conjecture (XOR recurrence bridge to A105033; worker oeis-102371)
- ACCEPTED OEIS-103425-conjecture (see `proofs/OEIS-103425-conjecture/Submission.lean`, ledger entry)
- ACCEPTED OEIS-108306-conjecture (see `proofs/OEIS-108306-conjecture/Submission.lean`, ledger entry)
- ACCEPTED OEIS-112970-conjecture1 (see `proofs/OEIS-112970-conjecture1/Submission.lean`, ledger entry)
- ACCEPTED OEIS-112970-conjecture2 (see `proofs/OEIS-112970-conjecture2/Submission.lean`, ledger entry)
- ACCEPTED OEIS-113250-conjecture (see `proofs/OEIS-113250-conjecture/Submission.lean`, ledger entry)
- ACCEPTED OEIS-113252-conjecture (see `proofs/OEIS-113252-conjecture/Submission.lean`, ledger entry)
- ACCEPTED OEIS-113255-conjecture (see `proofs/OEIS-113255-conjecture/Submission.lean`, ledger entry)
- ACCEPTED OEIS-237271-observation_carmichael (see `proofs/OEIS-237271-observation_carmichael/Submission.lean`, ledger entry)
- ACCEPTED OEIS-3625-conjecture (see `proofs/OEIS-3625-conjecture/Submission.lean`, ledger entry)

## Notes
- Counterexample-hunt problems (306477, 71532, 64169, 70823): no counterexamples in computed ranges; skipped.
- 176477-c1 (Sun integrality): p-adic supercongruence; formalization out of scope for budget; skipped after exploration (see scratch_176477_notes.md).
- Swarm: orchestrator + up to 6 subagents; per-problem scratch files kept in workspace.

## Not accepted (final status)

- OEIS-237271-conjecture_5 (`Odd (a (n * (2*n-1)))`, 497-line divisor-pairing parity proof):
  compiles CLEAN locally (`s237271c5.lean`, 0 errors; copy at `proofs/OEIS-237271-conjecture_5/Submission.lean`),
  but the referee run TIMED OUT (ledger 13:23:57, machine under heavy load during the run).
  Per honesty rule NOT counted as accepted.

Ledger complete: 15 entries, append-only; every referee run logged. Session closed.
