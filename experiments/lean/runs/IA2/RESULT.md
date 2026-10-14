```json
{"accepted": ["OEIS-103425-conjecture", "OEIS-70823-conjecture", "OEIS-112970-conjecture1", "OEIS-112970-conjecture2", "OEIS-100434-conjecture2", "OEIS-100434-conjecture3", "OEIS-113250-conjecture", "OEIS-113252-conjecture", "OEIS-113255-conjecture", "OEIS-108306-conjecture"]}
```

# RESULT — work/IA2 (CS8, single agent)

## Accepted (10)
| Problem | Approach |
|---|---|
| OEIS-103425-conjecture | witness a=1,b=0,c=0, x=const 4 |
| OEIS-70823-conjecture | n=20 counterexample 169, 6765-digit decide |
| OEIS-112970-conjecture1 | a(odd)=a(half) unfold helper + omega |
| OEIS-112970-conjecture2 | induction via a_odd helper |
| OEIS-100434-conjecture3 | zero_of_R strong induction on charpoly |
| OEIS-100434-conjecture2 | same + d_even + half_of |
| OEIS-113255-conjecture | signed b seq: b(n+2)=-4b(n+1)-81b n; a(2n+1)=(b n)^2 strong induction |
| OEIS-113252-conjecture | companion seq x: x(n+2)=-4x(n+1)-36x n; a(2n+1)=(2x n)^2 strong induction |
| OEIS-113250-conjecture | a(n+6)=4096a(n) via charpoly linarith + residues |
| OEIS-108306-conjecture | Dmaster strong-induction + Mchar matrix identity (zero case: 16 rfl entry lemmas + simp only; succ: pow_succ chain); twoStepInduction |

## Worked, not submitted
**Arxiv.2507.17780.2 tx_graffiti_conjecture_2** (Z(G) ≤ α(G)+1, connected subcubic, answer=False):
- Full Lean counterexample template `proofs/zf_full_test.lean` COMPILES (exit 0, no errors) on Petersen
  (n=10): `fromEdgeSet` graph + DecidableRel instance, computable zfStep/zfCl mirrors with
  cl_eq bridging to `zeroForcingClosure`, witness + minimality `decide` over all 1024 finsets,
  `zeroForcingNumber = 5` via sInf antisymmetry, `indepNum = 4` via bitmask formulation
  (Finset-bounded ∀ with or-bodies; Multiset-membership decide instances stuck on bound vars).
- Missing piece: an actual graph with Z ≥ α+2. Exhaustive: subcubic n ≤ 9, cubic n = 8, 10 — none.
  Generalized Petersen (10 families to n=20), truncated tetrahedron, 4000 random subcubic n=12..20 — none.
  n=10 subcubic, n=11/12/13 cubic exhaustive searches launched but did not finish within budget.
- GC59: n=8 exhaustive no counterexample; abandoned.

## Skipped
- 306477 (needs heavy machinery), 71532, 113252/113255 (time).
