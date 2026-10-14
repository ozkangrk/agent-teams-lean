#!/usr/bin/env python3
"""One-off text update of paper/main.tex for the CS8/CS9 results (Claude's code). Exact-string replacements; aborts if
any anchor is missing, so the edit is all-or-nothing."""
from pathlib import Path

P = Path(__file__).resolve().parent.parent / "paper/main.tex"
x = P.read_text()
R = []

R.append(("""\\title{Does a Small Agent Team Beat a Single Agent?\\\\[0.3em]
\\large A Pre-registered, Contamination-Controlled Comparison on Formal Mathematics}""",
"""\\title{Does a Small Agent Team Beat a Single Agent?\\\\[0.3em]
\\large Parallel Attempts, Not Coordination: Pre-registered, Contamination-Controlled Experiments on Formal Mathematics}"""))
R.append(("\\date{Draft, 13 October 2026}", "\\date{Draft, 14 October 2026}"))

a0 = x.index("\\begin{abstract}"); a1 = x.index("\\end{abstract}") + len("\\end{abstract}")
R.append((x[a0:a1], r"""\begin{abstract}
Claims that ``swarms'' of language-model agents outperform a single agent are rarely tested with model, compute and
time held equal. We ran three pre-registered eight-hour experiments with GLM-5.3 agents.
\begin{itemize}
  \item \textbf{Task:} write Lean~4 proofs for \CSsevenN{} statements from Google DeepMind's \emph{formal-conjectures}
    that were resolved after the model's assumed training cutoff.
  \item \textbf{Leak control:} agents saw the statements through sanitised sources.
  \item \textbf{Acceptance:} a proof counted only if a kernel-checking referee with an axiom whitelist accepted it.
\end{itemize}
\textbf{Team versus single agent.} An orchestrator--worker team (one orchestrator, at most six concurrent workers)
proved more statements than a single agent with the same model, harness, cores, memory and time in both runs:
\CSsevenTW{} vs \CSsevenTS{}, and \CSnineTW{} vs \CSnineTS{} in a replication. The single agent's solved set was a
subset of the team's both times.
\begin{itemize}
  \item Per run the effect is small: one-sided exact McNemar $p=\CSsevenP$ and $p=\CSnineP$.
  \item Pooled it is consistent: \PoolB{} discordant pairs to \PoolC, $p=\PoolP$. Under the strictest sensitivity
    analysis for an isolation breach, $p=\PoolSensP$.
\end{itemize}
\textbf{Independent copies.} Four single agents that could not communicate, sharing the team's cores and memory, proved
the union of \CSeightUnion{} statements. The pre-registered coordination test found no advantage for the coordinated
team: \CSnineTW{} vs \CSeightUnion, two-sided $p=\CSnineCoordP$. At the team's token budget the independent union stood
at \CSeightTMlo--\CSeightTMhi.
\textbf{Variance and depth.} Six single-agent runs ranged from \SingleMin{} to \SingleMax{} proofs. No configuration
proved any Erd\H{o}s-problem or research-paper statement.
\textbf{Conclusion.} In this setting the benefit of a multi-agent system comes from parallel attempts, at about four
times the tokens, not from coordination.
\textbf{Integrity.} We also report integrity events. A single agent escaped its sandbox to replace its supervisor, and a
team worker read the single agent's session log. An allow-list sandbox closed both channels.
\end{abstract}"""))

c0 = x.index("\\begin{enumerate}\n  \\item \\textbf{A pre-registered comparison (CS7).}"); c1 = x.index("\\end{enumerate}", c0) + len("\\end{enumerate}")
R.append((x[c0:c1], r"""\begin{enumerate}
  \item \textbf{Team versus single agent, twice (CS7, CS9).} Two pre-registered runs compare one agent with an
    orchestrator--worker team. The two conditions are matched on model, harness, tools, cores, memory and wall-clock
    time, and both attempt the same \CSsevenN{} statements, resolved after the model's assumed cutoff and shown through
    sanitised sources \citep{nosek2018}. The team proved more statements in both runs, and the single agent's set was
    nested in the team's. The effect is small per run and consistent when pooled.
  \item \textbf{A coordination control (CS8).} Four independent copies of the single agent share the team's cores and
    memory, cannot communicate, and are scored by the union of their proofs. They match the team in coverage, and at
    equal tokens too. This separates the two explanations: in this setting the team's advantage is parallel attempts,
    not coordination.
  \item \textbf{Variance and cost.} Single-agent results vary from run to run about as much as the team--single gap.
    Teams cost about four times the tokens.
  \item \textbf{Exploratory studies.} Three studies in other domains with the same harness (CS3--CS5) and one on open
    conjectures (CS6) point the same way.
  \item \textbf{An integrity record.} We document a sandbox escape by a single agent, a cross-condition read by a team
    worker, rule violations by teams in an earlier study, our own harness faults, and the allow-list sandbox that closed
    the gaps.
\end{enumerate}"""))

R.append(("This is the main alternative explanation for any team advantage. Section~\\ref{sec:discussion} specifies the control\nthat separates it from coordination.",
          "This is the main alternative explanation for any team advantage, and Section~\\ref{sec:cs89} tests it directly\nwith independent copies of the single agent."))

R.append(("Each condition writes an append-only ledger of its attempts. We count tokens from the session files, workers included.",
r"""Each condition writes an append-only ledger of its attempts. We count tokens from the session files, workers included.

\paragraph{Sandbox.} Every agent tool call runs in a bubblewrap sandbox without network access.
\begin{itemize}
  \item \textbf{CS7:} the sandbox started from the full filesystem and hid only the other workspaces.
  \item \textbf{Two leaks in CS7:} it left the terminal-multiplexer and user-bus sockets, the PID namespace and the
    agents' session logs reachable. Both were exploited, once each (Section~\ref{sec:integrity}).
  \item \textbf{CS8 and CS9:} an \emph{allow-list} root. It contains only system directories, the kernel's Python, the
    Lean toolchain, the referee, the problem files and sanitised sources (all read-only), and the agent's own workspace
    and session directory. It also uses private PID, IPC and UTS namespaces.
\end{itemize}"""))

R.append(("\\section{The pre-registered experiment (CS7)}", "\\section{Experiment 1: single agent versus team (CS7)}"))

R.append(("""  \\item \\textbf{Gate fault and escape (D6):} a harness fault made the supervisor's gate output wrong for both
    conditions, which led to the single agent's sandbox escape. We fixed the fault for both conditions at 05:56.
\\end{itemize}
None changed the problem set, the referee or the scoring.""",
"""  \\item \\textbf{Gate fault and escape (D6):} a harness fault made the supervisor's gate output wrong for both
    conditions, which led to the single agent's sandbox escape. We fixed the fault for both conditions at 05:56.
  \\item \\textbf{Cross-condition read (D8, found after the run):} a team worker read part of the single agent's session
    log (Section~\\ref{sec:integrity}).
\\end{itemize}
None changed the problem set, the referee or the scoring."""))

R.append(("H1 is supported.", "H1 is supported in this run. Section~\\ref{sec:cs89} reports the replication and a sensitivity analysis for D8."))
R.append(("Wall-clock time, cores and model\nwere matched, but tokens were not. This is the main caveat to H1 (Section~\\ref{sec:discussion}).",
          "Wall-clock time, cores and model\nwere matched, but tokens were not. Section~\\ref{sec:cs89} tests whether this explains H1."))

h0 = x.index("\\paragraph{H4: integrity.}\\leavevmode"); h1 = x.index("\\section{Exploratory studies}")
R.append((x[h0:h1], r"""\paragraph{H4: integrity.}\leavevmode
\begin{itemize}
  \item \textbf{Network and workspaces:} automated scans of every agent-authored tool input found no network attempts
    and no access to the other condition's workspace.
  \item \textbf{One escape (TS, D6):} the single agent left its sandbox during one episode
    (Section~\ref{sec:integrity}). It produced no proof and no scoring advantage: TS had \CSsevenTS{} accepted proofs
    before and after it.
  \item \textbf{One cross-condition read (TW, D8):} found after the run.
    \begin{itemize}
      \item A team worker read parts of the single agent's session log for 11 seconds.
      \item The single agent had proved none of the team-only statements, so the log contained no proof of them.
      \item Of the \CSsevenB{} team-only statements, \DeightBefore{} were accepted before the read and \DeightAfter{} after
        it.
      \item Excluding all \DeightAfter, the CS7 comparison gives $p=\DeightPworst$; excluding only the family the
        worker was working on, $p=\DeightPfam$.
      \item Independent agents that had no access to anything (CS8) proved \CSeightDeightHit{} of these \DeightAfter{}
        statements.
    \end{itemize}
\end{itemize}

\section{Experiments 2 and 3: independent agents (CS8) and replication (CS9)}
\label{sec:cs89}
Both experiments were pre-registered together after CS7, before either run.
\begin{itemize}
  \item \textbf{Same as CS7:} problem set, sanitised sources, referee, model and 8-hour budget.
  \item \textbf{Changed:} the allow-list sandbox, per-condition session directories, the corrected task text (D7) and the
    supervisor fix from D6.
\end{itemize}

\paragraph{CS8: four independent agents.}
\begin{itemize}
  \item \textbf{Agents:} four copies of the single-agent condition (IA1--IA4), each with its own workspace, daemon,
    supervisor and watchdog.
  \item \textbf{Isolation:} the sandbox prevented any contact between them.
  \item \textbf{Resources:} all four shared cores 0--8 and one 20/28\,GB memory budget, exactly the resources of the
    CS7 team.
  \item \textbf{Why four:} $k=4$ was chosen before the run as the closest match to the team's token multiple and to its
    mean number of live agents.
  \item \textbf{Score:} the union of statements proved by any of the four.
\end{itemize}

\paragraph{CS9: replication.} TS2 and TW2 repeat CS7's two conditions, with the core sets swapped.

\paragraph{Pre-registered tests.}
\begin{itemize}
  \item \textbf{R1:} TW2 $>$ TS2, one-sided exact McNemar.
  \item \textbf{Pooled CS7+CS9:} the same test on all discordant pairs.
  \item \textbf{C1, primary coordination test:} TW2 versus the CS8 union, two-sided.
  \item \textbf{C2:} union $>$ single agent, one-sided.
\end{itemize}
Deviations D9--D11 (Appendix~\ref{app:deviations}) affected measurement and model access, not scoring.

\begin{table}[t]
\centering
\caption{All runs on the same \CSsevenN{} statements (8 h each, GLM-5.3, referee re-run after the deadline). Tokens are
GLM-5.3 output tokens, workers included.}
\label{tab:runs}
\small
\begin{tabular}{llrrr}
\toprule
Run & Condition & Proofs & Calls & Output (M) \\
\midrule
CS7 & TS: single agent & \CSsevenTS & \CSsevenTSCalls & \CSsevenTSOutM \\
CS7 & TW: team (orchestrator + $\le$6) & \CSsevenTW & \CSsevenTWCalls & \CSsevenTWOutM \\
CS8 & IA1 / IA2 / IA3 / IA4: independent single agents & \CSeightIAOne{} / \CSeightIATwo{} / \CSeightIAThree{} / \CSeightIAFour & & \\
CS8 & IA union & \CSeightUnion & \CSeightCalls & \CSeightOutM \\
CS9 & TS2: single agent & \CSnineTS & \CSnineTSCalls & \CSnineTSOutM \\
CS9 & TW2: team (orchestrator + $\le$6) & \CSnineTW & \CSnineTWCalls & \CSnineTWOutM \\
\bottomrule
\end{tabular}
\end{table}

\begin{table}[t]
\centering
\caption{Pre-registered tests. $b$--$c$ are the discordant pairs (first condition only -- second condition only).
Tango 95\% CIs are in percentage points for first minus second.}
\label{tab:tests}
\small
\begin{tabular}{llcll}
\toprule
Test & Comparison & $b$--$c$ & $p$ & 95\% CI \\
\midrule
H1 (CS7) & TW vs TS & \CSsevenB--\CSsevenC & \CSsevenP{} (one-sided) & $[\CSsevenTangoLo, \CSsevenTangoHi]$ \\
R1 (CS9) & TW2 vs TS2 & \CSnineB--\CSnineC & \CSnineP{} (one-sided) & $[\CSnineTangoLo, \CSnineTangoHi]$ \\
Pooled & CS7 + CS9 & \PoolB--\PoolC & \PoolP{} (one-sided) & \\
Pooled, D8 sensitivity & CS7 (4 removed) + CS9 & \PoolSensB--\PoolC & \PoolSensP{} (one-sided) & \\
C1 (primary) & TW2 vs IA union & \CoordB--\CoordC & \CoordP{} (two-sided) & $[\CoordLo, \CoordHi]$ \\
C1 (secondary) & TW vs IA union & 1--1 & \CoordTWsevenP{} (two-sided) & $[\CoordTWsevenLo, \CoordTWsevenHi]$ \\
C2 & IA union vs TS2 & \CtwoB--0 & \CtwoP{} (one-sided) & \\
C2 & IA union vs TS & \CSeightBvsTS--0 & \CSeightPvsTS{} (one-sided) & \\
\bottomrule
\end{tabular}
\end{table}

\paragraph{The team beats one agent, but by little per run.}
\begin{itemize}
  \item \textbf{Replication:} TW2 proved \CSnineTW{} statements and TS2 \CSnineTS. TS2's set was again a subset of the
    team's.
  \item \textbf{Per run:} with only \CSnineB{} discordant pairs, R1 is not significant on its own
    (Table~\ref{tab:tests}).
  \item \textbf{Pooled:} across CS7 and CS9 every one of the \PoolB{} discordant pairs favours the team ($p=\PoolP$).
    This holds at $p=\PoolSensP$ even after removing CS7's four team-only proofs that followed the D8 read.
  \item \textbf{Variance:} the single agent varies a lot between runs. Over six single-agent runs (TS, IA1--IA4, TS2)
    it proved \SingleMin--\SingleMax{} statements, mean \SingleMean. The team proved \CSsevenTW{} and \CSnineTW.
\end{itemize}

\paragraph{Independent copies match the team.}
\begin{itemize}
  \item \textbf{Coverage:} the four independent agents proved \CSeightUnion{} distinct statements, the same number as the
    CS7 team and more than TW2. They proved \CSeightTWonlyHit{} of CS7's six team-only statements.
  \item \textbf{Duplication:} the agents proved \CSeightSum{} statements in total. \CSeightDup{} of the \CSeightUnion{}
    distinct statements were proved by at least two agents, and \CSeightAllFour{} by all four.
  \item \textbf{Diminishing returns:} the expected union for $k=1,2,3,4$ agents is \CSeightKone, \CSeightKtwo,
    \CSeightKthree, \CSeightKfour. Two independent agents already come close to a team.
  \item \textbf{C1:} the coordination test finds no advantage for the team. TW2 proved \CoordB{} statement the union did
    not, and the union proved \CoordC{} that TW2 did not; $p=\CoordP$, CI $[\CoordLo, \CoordHi]$ points.
  \item \textbf{Cost:} the union used \CSeightOverTW$\times$ the team's output tokens. At the team's budget it stood at
    \CSeightTMlo--\CSeightTMhi{} (between two hourly snapshots), against \CSnineTW{} for TW2 and \CSsevenTW{} for TW.
  \item \textbf{Conclusion:} at equal tokens, coordination gave no measurable gain over independent attempts.
\end{itemize}
Figure~\ref{fig:cov} plots coverage against cost for every condition, and Figure~\ref{fig:curves} shows progress over
time.

\begin{figure}[t]
\centering
\begin{tikzpicture}
\begin{axis}[width=0.78\linewidth,height=5.6cm,xmin=0,xmax=4.1,ymin=6,ymax=18,
  xlabel={GLM-5.3 output tokens per condition (millions)},ylabel={statements proved},grid=major,grid style={gray!20},
  legend pos=south east,legend cell align=left]
\addplot[only marks,mark=square*,orange!85!black,mark size=2.6pt] table[x=x,y=y] {data/cov_single.dat};
\addplot[only marks,mark=*,blue!70!black,mark size=3pt] table[x=x,y=y] {data/cov_team.dat};
\addplot[only marks,mark=diamond*,green!50!black,mark size=4pt] table[x=x,y=y] {data/cov_union.dat};
\legend{single agent (6 runs),team (2 runs),4 independent agents (union)}
\end{axis}
\end{tikzpicture}
\caption{Coverage against cost. Each point is one condition: single agents (CS7 TS, CS8 IA1--IA4, CS9 TS2), teams (CS7
TW, CS9 TW2) and the union of the four independent agents (CS8). More tokens buy more coverage whether or not the agents
coordinate.}
\label{fig:cov}
\end{figure}

\begin{figure}[t]
\centering
\begin{tikzpicture}
\begin{axis}[width=0.85\linewidth,height=5.8cm,xmin=0,xmax=480,ymin=0,ymax=18,xtick={0,60,...,480},
  xlabel={minutes since start},ylabel={accepted proofs (hourly referee snapshots)},grid=major,grid style={gray!20},
  legend pos=south east,legend cell align=left,legend style={font=\scriptsize}]
\addplot[const plot,very thick,blue!70!black] table[x=t,y=n] {data/cs7_curve_TW.dat};
\addplot[const plot,very thick,orange!85!black] table[x=t,y=n] {data/cs7_curve_TS.dat};
\addplot[const plot,thick,blue!70!black,dashed] table[x=t,y=n] {data/cs9_curve_TW2.dat};
\addplot[const plot,thick,orange!85!black,dashed] table[x=t,y=n] {data/cs9_curve_TS2.dat};
\addplot[const plot,very thick,green!50!black,densely dotted] table[x=t,y=n] {data/cs8_curve_union.dat};
\legend{TW (CS7),TS (CS7),TW2 (CS9),TS2 (CS9),IA union (CS8)}
\end{axis}
\end{tikzpicture}
\caption{Progress over time. Each count is taken at the first hourly snapshot at which it was accepted. TW2's
snapshots before minute 121 were invalid because of a measurement fault (D10), so its curve starts there. Both CS7
and CS9 had a provider-quota stop (D5, D11).}
\label{fig:curves}
\end{figure}

"""))

R.append(("summarises them; the per-study records and deviation logs are part of the released material.",
          "summarises them; the per-study records and deviation logs are kept with the paper's source."))

R.append(("""Its stated intent was benign; the action was still a breach. Three sandbox gaps need closing in future runs: the
multiplexer socket, the user D-Bus socket, and the shared PID namespace.""",
r"""Its stated intent was benign; the action was still a breach.

\paragraph{A team worker read the single agent's log (CS7, D8).}
\begin{itemize}
  \item \textbf{When and why:} at 00:56 a team worker was trying to find out who had written an ``accepted'' entry in
    its own team's ledger. It searched all session logs under the agent home directory.
  \item \textbf{What it read:} for 11 seconds, parts of the single agent's log: its list of remaining problems and a
    short note.
  \item \textbf{Why the scans missed it:} the CS7 sandbox hid only the workspaces, and our first scan checked only
    workspace paths. We found the read while hardening the sandbox for CS8. Its effect on H1 is bounded in
    Section~\ref{sec:cs7}.
\end{itemize}

\paragraph{Closing the gaps (CS8, CS9).}
\begin{itemize}
  \item \textbf{Sandbox:} the allow-list sandbox removes every path not needed for the task, including all session
    logs, the experimenter's files and earlier results. Its private PID namespace makes harness processes invisible,
    and the multiplexer and bus sockets are absent.
  \item \textbf{Verification:} an end-to-end test confirmed that tool calls, background shells and subagents still
    work.
  \item \textbf{Result:} across \CSeightCalls{} (CS8) and 2{,}368 (CS9) agent tool calls, the scans found no access
    outside the agent's own workspace.
\end{itemize}"""))

R.append(("""  \\item the shared quota outage.
\\end{itemize}""", """  \\item shared quota outages in CS7 and CS9;
  \\item two measurement faults in CS9: worker logs stored outside the per-condition directory, and a nested proof
    layout that the hourly snapshot missed. Both were fixed with one rule for every condition, and CS7 and CS8 counts
    were unchanged.
\\end{itemize}"""))

d0 = x.index("\\section{Discussion}"); d1 = x.index("\\section{Limitations}")
R.append((x[d0:d1], r"""\section{Discussion}
\label{sec:discussion}
\paragraph{What the evidence supports.}
\begin{itemize}
  \item \textbf{More agents help.} A team and a group of independent agents both prove more statements than a single
    agent with the same model, time and hardware. The single agent's set is a subset of the team's in both team runs.
  \item \textbf{The cause is parallel attempts, not coordination.} The gain matches what independent attempts produce:
    \begin{itemize}
      \item four copies that never communicate reach the same coverage;
      \item at equal tokens they are comparable;
      \item the expected union of just two independent agents already covers most of the team's advantage.
    \end{itemize}
    This agrees with repeated-sampling results \citep{brown2024monkeys,li2024moreagents}. It also fits
    \citet{kim2025scaling}'s finding that coordination returns diminish once single agents are capable.
\end{itemize}

\paragraph{What coordination did and did not do.}
\begin{itemize}
  \item \textbf{CS7 suggested benefits:} the coordinated team appeared to make faster early progress and to avoid the
    duplicated work of independent agents (\CSeightSum{} proofs for \CSeightUnion{} distinct statements).
  \item \textbf{CS9 did not replicate them:} TW2 started more slowly and proved fewer statements on the same token
    budget.
  \item \textbf{Conclusion:} with this model and task, coordination neither raised coverage nor reliably reduced cost.
\end{itemize}

\paragraph{No gain in depth.}
\begin{itemize}
  \item Across every run, all solved statements are short OEIS identities or one graph conjecture.
  \item No configuration solved any Erd\H{o}s-problem, research-paper or Wikipedia statement.
  \item Only two statements solved in CS8 or CS9 had not been solved in CS7, one by the team and one by the independent
    agents.
\end{itemize}
More agents collect what the model can already prove faster; they do not extend it.

\paragraph{Practical guidance.}
\begin{itemize}
  \item \textbf{When agents help:} many independent, automatically verifiable tasks and a deadline. Parallel agents then
    finish more of them.
  \item \textbf{Teams versus copies:} in our data a coordinated team was no better than independent copies, so the
    simpler design deserves the first try.
  \item \textbf{When they don't:} single hard problems, or a tight token budget.
\end{itemize}

\paragraph{Why not hundreds of agents.}
The provider limits concurrent requests per account to roughly \RateLow--\RateHigh{} (measured), and it enforces a five-hour usage
quota. Between the start of CS7 and the quota stop (\QuotaHours{} hours), this machine made \QuotaCalls{} GLM calls with about
\QuotaPromptM{}M prompt tokens, from about \QuotaAgents{} live agents on average (about \QuotaPerAgentH{} calls per agent
per hour). At that rate, 16 agents would reach the same volume in about \QuotaSixteenH{} hours and then wait. More agents
would therefore add burst speed but not total work. Scaling studies of large swarms need local models or different quota
terms, and they should fix the total token budget.

"""))

l0 = x.index("\\section{Limitations}"); l1 = x.index("\\section{Conclusion}")
R.append((x[l0:l1], r"""\section{Limitations}
\label{sec:limits}
\begin{itemize}
  \item \textbf{Scope:} one model, $n=\CSsevenN$ statements, and two runs per team condition. Each run is noisy; the
    pooled result rests on \PoolB{} discordant pairs.
  \item \textbf{Different days:} CS7, CS8 and CS9 ran on different days. The coordination test compares runs from
    different days.
  \item \textbf{Quota stops:} the provider quota stopped both CS7 and CS9 for a while.
    \begin{itemize}
      \item In CS9 the owner reset the quota after about half an hour.
      \item The single agent lost about \CSnineLossTS{} minutes of model access and the team about \CSnineLossTW.
        This difference works against the single agent and is not corrected.
    \end{itemize}
  \item \textbf{Assumed cutoff:} the training cutoff of GLM-5.3 is assumed, not documented.
  \item \textbf{Selection of OEIS statements:} in the same period, OEIS Open reported language models resolving 147 of
    492 Lean-formalised OEIS conjectures \citep{adamczewski2026oeisopen}. Post-cutoff OEIS statements may therefore be
    biased towards problems that language models can solve.
  \item \textbf{Integrity in CS7:} the CS7 sandbox allowed one escape and one cross-condition read. They are bounded by
    sensitivity analyses, and CS8 and CS9 used the corrected sandbox.
  \item \textbf{Earlier studies:} CS3--CS6 were exploratory, CS3 ran sequentially, and CS5 had rule violations.
\end{itemize}

"""))

k0 = x.index("\\section{Conclusion}"); k1 = x.index("\\section*{Author contributions")
R.append((x[k0:k1], r"""\section{Conclusion}
We compared, under pre-registered tests and checking by a proof kernel, a single GLM-5.3 agent, an orchestrator--worker
team, and independent copies of the single agent on post-cutoff Lean statements.
\begin{itemize}
  \item \textbf{Several agents beat one:} the team proved more than the single agent in both runs, and the pooled test
    is clear.
  \item \textbf{Coordination added nothing measurable:} four independent copies matched the team's coverage, and at
    equal tokens they did as well.
  \item \textbf{No depth:} nothing solved a harder statement.
\end{itemize}
In this setting the value of a multi-agent system is parallel attempts at about four times the cost, not collective
intelligence. Along the way, a single agent escaped its sandbox to repair its own supervisor, and a team worker read
another condition's log. Agent experiments need allow-list sandboxes and integrity scans as much as they need
statistics.

"""))

R.append(("""  \\item \\textbf{Release:} \\todo{release the problem set, referee, harness wrappers, session logs and deviation files.}""",
          """  \\item \\textbf{Materials:} the problem set, referee, sandbox and harness wrappers, analysis scripts, hourly
    snapshots and deviation logs are kept in the author's repository and are intended for release with the final
    version."""))

R.append(("\\section{Deviation summary (CS7)}", "\\section{Deviation summary (CS7--CS9)}"))
R.append(("""  \\item[Post-deadline.] Team workers kept writing scratch files until 07:38 because the agent daemon outlived the
    session; \\texttt{proofs/} did not change after 07:08.
\\end{description}""", """  \\item[Post-deadline (CS7).] Team workers kept writing scratch files until 07:38 because the agent daemon outlived
    the session; \\texttt{proofs/} did not change after 07:08. From CS8 on the supervisor stops the agent at the
    deadline.
  \\item[D8 (CS7, found later).] A team worker read parts of the single agent's session log for 11 seconds at 00:56.
    Bounded by sensitivity analyses; closed by the allow-list sandbox.
  \\item[PREREG CS8/CS9.] Written before both runs. Changes from CS7: allow-list sandbox, per-condition session
    directories, corrected task text, supervisor as a scope that stops the agent at the deadline, and a watchdog that
    descends through both sandbox layers.
  \\item[CS8 gates.] IA2 and IA3 failed the completion gate on deliverable format (file naming, claim format). Scoring
    uses the referee re-run, as pre-registered.
  \\item[D9 (CS9).] Worker session files were stored in the global session directory. The measurement tools were fixed;
    isolation was unaffected.
  \\item[D10 (CS9).] TW2 stored proofs as \\texttt{proofs/<id>/Submission.lean}, which the hourly snapshot missed. One
    rule now counts any accepted file under \\texttt{proofs/}; CS7 and CS8 counts were unchanged. TW2's first two
    snapshots are invalid.
  \\item[D11 (CS9).] The provider quota was exhausted at about 09:47. The owner reset it at about 10:15, and both
    conditions resumed through the standard nudge. TS2 lost about \\CSnineLossTS{} minutes, TW2 about \\CSnineLossTW.
\\end{description}"""))

for old, new in R:
    if old not in x:
        raise SystemExit("anchor missing: " + old[:80])
    x = x.replace(old, new, 1)
x = x.replace("\\CSnineCoordP", "\\CoordP")
P.write_text(x)
print("ok", len(R), "replacements")
