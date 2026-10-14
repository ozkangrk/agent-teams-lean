# WORKFLOW (swarm proof protocol)

Workspace: /home/ozkangu/Desktop/research/10-swarm-lean/work/TW2
Upstream repo (read-only): ../../upstream/formal-conjectures
OEIS metadata: ../../library/oeis/A<N>.json  (problems reference A-numbers, e.g. "OEIS-109074" = A109074)

## Per-problem loop
1. `python3 stmt.py <problem-id>`  -> prints upstream module, theorem, statement text, and upstream file path.
2. Read the upstream .lean file: definitions + statement + test theorems show small values (useful!).
3. Explore definitions in scratch files `scratch_<id>.lean` with `#eval`/`example` (scratch is never checked).
   Compile scratch: `../../tools/lean.sh scratch_<id>.lean`
4. Write submission `proofs/<problem-id>/Submission.lean`:
   - first line: `import <upstream module>` (module string printed by stmt.py, with « » quotes where needed)
   - then: `theorem swarm_proof : <STATEMENT COPIED VERBATIM> := by ...`  (or `swarm_disproof` proving the negation)
   - NO `sorry`, NO metaprogramming, NO `native_decide`/`decide +native`, NO `#eval`, NO custom axioms,
     NO `namespace`/`section` (referee regex), only `set_option maxHeartbeats/maxRecDepth` allowed.
   - `decide` (kernel) is allowed. `simp`, `omega`, `norm_num`, `ring` etc. all allowed.
5. Compile it: `../../tools/lean.sh proofs/<id>/Submission.lean` (few seconds).
6. Referee: `python3 ref.py <problem-id> proofs/<id>/Submission.lean <your-name>` (appends verdict to ledger.jsonl).
7. On acceptance: keep the file, move on. On rejection: read verdict JSON, fix, retry. Do not delete attempts.

## Notes
- `answer(x)` in a statement elaborates to an annotated `x`; keep it verbatim.
- Statement text must be copied EXACTLY (binders, hypotheses, instance args) from the upstream file.
- Referee timeout ~1200s; keep decide-checks small enough to finish (<5 min).
- Honesty: an id counts as DONE only after referee verdict `"accepted": true`.
- Use `rlm.progress_note("...")` for brief progress; message parent when your batch is done or stuck.
