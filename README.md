# Does a Small Agent Team Beat a Single Agent? Parallel Attempts, Not Coordination

This repository holds the materials for the paper. The compiled paper is `paper/agent-teams-lean.pdf`.

**Study design.** Several GLM-5.3 agent configurations wrote Lean 4 proofs for 100 statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `79222608`). All
100 statements were resolved after the model's assumed training cutoff. Agents saw the statements through sanitised
sources, and a proof counted only if a kernel-checking referee with an axiom whitelist accepted it. Three experiments
were pre-registered:

| Run | Conditions (8 h each) | Statements proved |
|---|---|---|
| CS7 | single agent (TS) vs orchestrator–worker team (TW, ≤ 6 workers) | 10 vs 16 |
| CS8 | four independent single agents (IA1–IA4), same cores and memory as the team | 14, 10, 14, 8; union 16 |
| CS9 | replication of CS7 with the core sets swapped (TS2 vs TW2) | 11 vs 13 |

**Main result.**
- **Team vs single agent:** the team beats a single agent (pooled CS7 + CS9: 8 discordant pairs to 0, p = 0.004).
- **Coordination:** the pre-registered coordination test (TW2 vs the IA union: 13 vs 16, p = 0.375) found no
  advantage for coordination. At equal token budgets the two are comparable.
- **Conclusion:** the gain comes from parallel attempts, not coordination.

## Who did what
- **Author:** G. Ozkan conceived and designed the study, directed the work and checked the results.
- **AI assistance:** an AI coding assistant (Claude, Anthropic) worked under the author's direction. It wrote the code
  in this repository (referees, sandboxes, supervisors, watchdogs, analysis and paper-build scripts), ran and
  monitored the experiments, kept the deviation logs and evaluation notes, and drafted the paper. It is the
  "experimenter" named throughout the records (for example `PREREG_CS7.md`, `DEVIATIONS.md`, `evaluations.md`), and
  "Claude's code" in file headers refers to it.
- **Agents under study:** GLM-5.3 agents running in Prime Agent.

## Layout
- **`paper/`:** LaTeX source; `make` rebuilds numbers, bibliography and PDF.
  - `scripts/build_data.py` generates every number in the text from `paper/records/`.
  - `scripts/build_bib.py` fetches and verifies every citation from the arXiv API or doi.org.
- **`harness/`:** experimenter code.
  - Kernel sandboxes: `kernel_sandbox.sh` (CS6–CS7) and the allow-list `kernel_sandbox_v2.sh` (CS8–CS9).
  - Run control: supervisor, watchdog, referee snapshots, completion gate.
  - Measurement: integrity scan and token accounting.
- **`experiments/lean/conditions/`:**
  - Pre-registrations: `PREREG_CS7.md`, `PREREG_CS8_CS9.md`.
  - Records: deviation log `DEVIATIONS.md`, evaluations, problem set `cs7_set.jsonl`.
  - Agent instructions: task and agent texts.
  - Scripts and outputs: launchers, analysis scripts and their outputs, hourly referee snapshots, launch log.
- **`experiments/lean/referee/`:**
  - `check.py`: the referee, with a self-test of cheating attempts and disproofs.
  - `sanitize.py`: builds the leak-free views.
  - `extract.py`: problem extraction.
- **`experiments/lean/runs/<condition>/`:** per condition:
  - every Lean proof file;
  - the experimenter's final referee verdicts (re-run after the deadline);
  - append-only ledgers, deliverables, and supervisor and watchdog logs.

  Conditions: P1 and O1 (CS6), TS and TW (CS7), IA1–IA4 (CS8), TS2 and TW2 (CS9).
- **`experiments/exploratory/`:** exploratory studies CS3–CS5 (GPU kernels, extremal constructions, HorizonMath), with
  their task texts, evaluations, deviation logs, referees and final verdicts.

## Not included
- **Raw agent session transcripts:** large, and they include tool output from the machine.
- **The formal-conjectures checkout:** use commit `79222608`.
- **The OEIS entries:** these are third-party data. `referee/sanitize.py` regenerates the sanitised views from a
  formal-conjectures checkout and OEIS JSON entries.

## Third-party material
The problem files (`experiments/lean/conditions/*.jsonl` with a `statement` field, and `paper/records/cs7_set.jsonl`)
contain statement text from google-deepmind/formal-conjectures, which is licensed under Apache-2.0. The proofs under
`experiments/lean/runs/` restate those statements. See [`NOTICE`](NOTICE) for the attribution and
[`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt) for the licence text.

## Licence
- **Code** (`harness/`, `experiments/*/referee/`, `experiments/lean/tools/`, the analysis and launch scripts in
  `experiments/lean/conditions/`, `paper/scripts/`, `paper/Makefile`): MIT, see [`LICENSE`](LICENSE).
- **Data, records and the paper** (pre-registrations, deviation logs, evaluations, snapshots, ledgers, verdicts, logs,
  the agents' proofs and notes under `experiments/*/runs/`, `paper/*.tex`, `paper/refs.bib`, the PDF and figure data):
  CC BY 4.0, see [`LICENSES/CC-BY-4.0.txt`](LICENSES/CC-BY-4.0.txt).
- **Third-party material keeps its own terms:** the formal-conjectures statement text is Apache-2.0 (see
  [`NOTICE`](NOTICE)); any OEIS text reaching these files through formal-conjectures follows the OEIS terms.

## Pre-registration timeline
Recorded in the author's local git history; commit hash and timestamp (UTC+3).

| Event | Commit | Time |
|---|---|---|
| CS7 pre-registration | `190f28e` | 2026-10-12 20:47 |
| CS7 amendment A1 (post-cutoff problem set, sanitised views) | `f5ad977` | 2026-10-12 20:58 |
| CS7 amendment A2 (infrastructure) | `3dd8373` | 2026-10-12 23:08:04 |
| CS7 launch | `bf390fb` | 2026-10-12 23:08:50 (agents started 23:08:10) |
| CS8/CS9 pre-registration | `b1de97b`, `c05b481` | 2026-10-13 17:43:12 / 17:43:19 |
| CS8 launch | — | 2026-10-13 17:43:27 |
| CS9 launch | `ed904f4` | 2026-10-14 07:11:41 |

All deviations from the plans are listed with timestamps in `experiments/lean/conditions/DEVIATIONS.md` (D1–D11).
