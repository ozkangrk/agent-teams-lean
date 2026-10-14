# TRIAGE (CS7/CS8 single agent, 8h budget)

Legend: E = easy/mechanical, M = medium (1-3h), H = hard (skip unless time left)

## Tier E (attempt first)
- OEIS-103425: constant witness x=4, coeffs (1,0,0). E
- OEIS-112970-conjecture1/2: unfold `a` once / induction on n. E
- OEIS-306477: single counterexample n, bounded decide. E (after search)
- OEIS-71532-conjecture1: counterexample n with a n <= 0, decide. E
- OEIS-70823: counterexample n, decide/norm_num. E/M
- ErdosProblems-348: set equality, monotone seq + additively-complete. M-H (park)

## Tier M
- OEIS-113250/113252/113255: closed-form (2^n exponent) by strong induction. M
- OEIS-100434-conjecture1/2/3: two-step induction on parity subsequences. M
- OEIS-3625: disc -7 nonsquare mod p iff p%7 in {3,5,6} (quad. reciprocity). M
- 2507.17780 tx_graffiti_2: find small counterexample graph, decide. M
- WrittenOnTheWallII 59/194/200/291: find counterexample graphs. M-H
- OEIS-64169: harmonic num-den divisibility counterexample. M (size?)
- OEIS-48153: sum of k^2 mod n <= (n^2-1)/2. M-H
- 2605.12342 gammaSubgroup 2-generation. M-H
- OEIS-108306 invertSeqD = genMatrix^n. M-H
- OEIS-22030 invariant -> linear recurrence. M-H

## Tier H (skipped)
Everything else: research-level (Borsuk, Sendov, Kaplansky, Sidorenko, Komlos,
Brennan, Pompeiu, hyperbolic groups, permanents, Cohn-Elkies, spectral sets,
Erdos 1/181/371/421/424/469/477/486/547/548/952/968/970/973/1041/172, Chvatal,
ClaudesCycles, TuDeng, MicroscopicWeighting, TensorRank, IndependentDomination,
solvable_of_cyc_lt, A105565, A109074, A112521, A129365, A141057, A176477,
A185895, A211417, A237271, A3162, A49473, A53175, A93456, A102371, A105801,
A108081, A287616, A100474, A76141, AME 12 5, eqSystem10, Green16/29, ...)
