# RESULT — IA4 (CS8, single agent)

## Score: 8 problems from PROBLEMS.jsonl accepted by the referee (plus bonus theorem OeisA112970.conjecture3)

All proofs live in `proofs/*.lean`, format `import <module>` + `theorem swarm_proof : <statement>`.
Every attempt is logged in `ledger.jsonl` (append-only).

```json
{"accepted": ["OEIS-103425-conjecture", "OEIS-112970-conjecture1", "OEIS-112970-conjecture2", "OEIS-70823-conjecture", "OEIS-3625-conjecture", "OEIS-100434-conjecture2", "OEIS-100434-conjecture3", "OEIS-113250-conjecture"]}
```

All 8 above were re-verified with the referee at session end (2026-10-13, all `accepted: true`; A103425 took 837s on a cold import, the rest ~6s). A ninth proof (OeisA112970.conjecture3, in `proofs/OEIS-112970-conjecture3.lean`) compiles and was accepted mid-session, but its theorem is not in the sanitized module / PROBLEMS.jsonl, so it is not counted.


### Accepted (9)
| # | Problem | Module / theorem | Idea |
|---|---------|------------------|------|
| 1 | OEIS A103425 | OeisA103425.conjecture | decide-level computation |
| 2 | OEIS A112970 c1 | OeisA112970.conjecture1 | small-number verification |
| 3 | OEIS A112970 c2 | OeisA112970.conjecture2 | small-number verification |
| 4 | OEIS A112970 c3 | OeisA112970.conjecture3 | small-number verification |
| 5 | OEIS A70823 | OeisA70823.conjecture | divisibility computation |
| 6 | OEIS A3625 | OeisA3625.conjecture | quadratic residues over ZMod 7, top-level Fact lemmas, `linear_combination` certificates via Legendre symbols |
| 7 | OEIS A100434 c2 | OeisA100434.conjecture2 | paired even-witness existentials; `Nat.twoStepInduction`; recurrences by `rfl`; `linarith` |
| 8 | OEIS A100434 c3 | OeisA100434.conjecture3 | two-step inductions relating a,c,d subsequences; parity split |
| 9 | OEIS A113250 | OeisA113250.conjecture | `a(n+6) = 4096*a(n)` by strong induction; `64^m` square witnesses per `n % 3` |

### Main failed directions (details in ledger.jsonl)
- **A113252 / A113255**: odd terms are all squares, but sqrt subsequence is provably NOT a linear recurrence (checked orders ≤ 6 over exact Fractions); closed-form cross-term analysis kills all linear-recurrent witness forms. Needs a nonlinear (Somos-type) witness — research level, abandoned.
- **A64169** (harmonic H(n).num − H(n).den primality): statement holds for all n ≤ 3002; known counterexample larger; exact ℚ computation in the Lean kernel infeasible.
- **WrittenOnTheWallII 59/194/200/291** (refutable graph conjectures): exhaustive + pool searches found **no** counterexample on any connected graph with n ≤ 8 (python exhaustive n ≤ 7; C enumeration of the non-Dirac pool {∃ vertex deg ≤ 3} at n = 8, plus complements for 291; DP traceability check; correct induced-forest = acyclic definition). Refutation graphs must need n ≥ 9, beyond reachable search space in budget.
- **Arxiv.2507.17780 tx_graffiti_conjecture_2** (Z(G) ≤ α(G)+1 for connected subcubic non-K4): target of a full Lean refutation pipeline. List-bridge scaffold (`proofs/scratch-g18.lean`) compiles cleanly: Petersen graph `GP` on Fin 10 via `SimpleGraph.mk'` + pattern-match `adjB`, `zfStepC`↔`stepL` bridge (`mem_step_iff`, `mem_iter_iff` over `sortedOf S = (finRange 10).filter (· ∈ S)`), α(GP)=4 via `IsIndepSet.card_le_indepNum`/`exists_isNIndepSet_indepNum` + 5-subset extraction, `znum` bounds via `Nat.sInf_le`/`Nat.sInf_mem`, connectivity via explicit `Walk.cons` chains, degree by `maxDegree_le_of_forall_degree_le`. Remaining kernel `decide`s (no forcing set of size ≤ 4 over 1024 sublists; 5-sublist independence) did not finish: `lean -j2` degrades to <10% CPU at 13–21GB RSS. Search side: exhaustive n=9 clean (all 80.5M connected subcubic graphs), n=10 C search killed at 2h08 with no hit. No counterexample in reach; Petersen itself satisfies Z=5=α+1. Not submitted.
- Others (A71532, A306477, A49473, A53175, A76141, A93456, Erdős family, IndependentDomination, TuDeng, mathoverflow_1973, A105565): each attempted and logged; hard analytic content or out of reach.

## Environment notes
- Referee: `python3 -I ../../referee/check.py --module M --theorem T --proof P`; native_decide forbidden.
- Axioms allowed: Classical.choice, Quot.sound, propext (all accepted proofs use at most these).
