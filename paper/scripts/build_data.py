#!/usr/bin/env python3
"""Build every number and plot table used by the paper from the experiment records (Claude's code).

    build_data.py

Reads the case-study records under ~/Desktop/research (never edits them), copies the inputs into data/ with a sha256
manifest, and writes:
- paper/numbers.tex: one \\newcommand per number quoted in the text (the paper never types a result by hand);
- paper/data/*.dat: tables for the pgfplots figures.
"""
import glob, hashlib, json, math, os, shutil
from datetime import datetime, timezone
from pathlib import Path

R = Path.home() / "Desktop/research"
OUT = Path(__file__).resolve().parent.parent
L = R / "10-swarm-lean"
SRC = {
    "cs7_analysis.json": L / "conditions/cs7_analysis.json",
    "cs7_set.jsonl": L / "conditions/cs7_set.jsonl",
    "cs7_snapshots.jsonl": L / "conditions/snapshots.jsonl",
    "cs7_TS_ledger.jsonl": L / "work/TS/ledger.jsonl",
    "cs7_TW_ledger.jsonl": L / "work/TW/ledger.jsonl",
    "token_account.json": L / "conditions/token_account.json",
    "cs7_TS_final_verdict.json": L / "work/TS/final_verdict.json",
    "cs7_TW_final_verdict.json": L / "work/TW/final_verdict.json",
    "cs4_S1_final_verdict.json": R / "08-swarm-math/work/S1/final_verdict.json",
    "cs4_S2_final_verdict.json": R / "08-swarm-math/work/S2/final_verdict.json",
    "cs5_S1_final_verdict.json": R / "09-swarm-hard/work/S1/final_verdict.json",
    "cs5_S2_final_verdict.json": R / "09-swarm-hard/work/S2/final_verdict.json",
    "cs5_S3_final_verdict.json": R / "09-swarm-hard/work/S3/final_verdict.json",
    "cs3_C1_gate_verdict.json": R / "07-swarm-engineering/verdicts/20261011-130451-C1-gate/verdict.json",
    "cs3_C1_final_verdict.json": R / "07-swarm-engineering/verdicts/20261011-112557-C1-final/verdict.json",
    "cs3_C2_final_verdict.json": R / "07-swarm-engineering/verdicts/20261011-160918-C2-final2/verdict.json",
    "cs3_C1_hidden.log": R / "07-swarm-engineering/conditions/C1_hidden.log",
    "cs3_C2_hidden.log": R / "07-swarm-engineering/conditions/C2_hidden.log",
    "cs6_P1_final_verdict.json": L / "work/P1/final_verdict.json",
    "cs6_O1_final_verdict.json": L / "work/O1/final_verdict.json",
    "cs8_analysis.json": L / "conditions/cs8_analysis.json",
    "cs9_analysis.json": L / "conditions/cs9_analysis.json",
    **{f"cs8_{c}_final_verdict.json": L / f"work/{c}/final_verdict.json" for c in ("IA1", "IA2", "IA3", "IA4")},
    **{f"cs9_{c}_final_verdict.json": L / f"work/{c}/final_verdict.json" for c in ("TS2", "TW2")},
}
(OUT / "data").mkdir(exist_ok=True)
man = {}
for k, p in SRC.items():
    shutil.copy(p, OUT / "data" / k)
    man[k] = {"source": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
(OUT / "data/MANIFEST.json").write_text(json.dumps(man, indent=1))
D = lambda k: json.loads((OUT / "data" / k).read_text())

M = {}  # macro name -> LaTeX text


def num(x, d=0):
    return f"{x:,.{d}f}".replace(",", "{,}")


# ---------------- CS7 ----------------
a = D("cs7_analysis.json")
h1 = a["H1"]
M |= {"CSsevenN": a["N"], "CSsevenTS": len(a["accepted"]["TS"]), "CSsevenTW": len(a["accepted"]["TW"]),
      "CSsevenBoth": len(a["both"]), "CSsevenB": h1["b_TW_only"], "CSsevenC": h1["c_TS_only"],
      "CSsevenP": f"{h1['p_one_sided']:.4f}", "CSsevenDiff": f"{h1['diff'] * 100:.0f}",
      "CSsevenCondLo": f"{h1['exact_conditional_CI95'][0] * 100:.1f}", "CSsevenCondHi": f"{h1['exact_conditional_CI95'][1] * 100:.1f}",
      "CSsevenTangoLo": f"{h1['tango_CI95'][0] * 100:.1f}", "CSsevenTangoHi": f"{h1['tango_CI95'][1] * 100:.1f}",
      "CSsevenFiles": h1["cluster_files"]["n_files"], "CSsevenFileB": h1["cluster_files"]["TW_only"],
      "CSsevenFileC": h1["cluster_files"]["TS_only"], "CSsevenFileP": f"{h1['cluster_files']['p_one_sided']:.3f}"}
probs = [json.loads(l) for l in (OUT / "data/cs7_set.jsonl").read_text().splitlines() if l.strip()]
src = a["by_source"]
nice = {"OEIS": "OEIS", "ErdosProblems": "Erd\\H{o}s problems", "WrittenOnTheWallII": "Written on the Wall II",
        "Arxiv": "arXiv papers", "Wikipedia": "Wikipedia", "Paper": "Other papers", "GreensOpenProblems": "Green's open problems",
        "Other": "Other", "Books": "Books", "Mathoverflow": "MathOverflow", "OpenQuantumProblems": "Open quantum problems"}
rows = sorted(src.items(), key=lambda kv: -kv[1]["n"])
M["CSsevenSourceRows"] = " ".join(f"{nice.get(k, k)} & {v['n']} & {v['TS']} & {v['TW']} \\\\" for k, v in rows)
h6 = a["H6"]
mon = {"2026-08": "August", "2026-09": "September", "2026-10": "October"}
M["CSsevenMonthRows"] = " ".join(f"{mon[m]} 2026 & {v['n']} & {v['TS']} & {v['TW']} \\\\" for m, v in sorted(h6.items()))
for m, v in h6.items():
    key = {"2026-08": "Aug", "2026-09": "Sep", "2026-10": "Oct"}[m]
    M |= {f"CSseven{key}N": v["n"], f"CSseven{key}TS": v["TS"], f"CSseven{key}TW": v["TW"]}
M["CSsevenOEISN"] = src["OEIS"]["n"]; M["CSsevenOEISTS"] = src["OEIS"]["TS"]; M["CSsevenOEISTW"] = src["OEIS"]["TW"]
M["CSsevenErdosN"] = src["ErdosProblems"]["n"]
# H2 (pre-registered): Claude's hourly referee snapshots -> step tables (count known at each snapshot time).
# Proof-file creation times are NOT used: a file can be created early and completed hours later.
START = 1791835690  # 2026-10-12 23:08:10 +03
snaps = [json.loads(l) for l in (OUT / "data/cs7_snapshots.jsonl").read_text().splitlines() if '"cond": "T' in l]
def minutes(t):  # snapshot "t" is local time (+03)
    return (datetime.fromisoformat(t).replace(tzinfo=timezone.utc).timestamp() - 3 * 3600 - START) / 60
for cn in ("TS", "TW"):
    pts = [(minutes(x["t"]), x["n_accepted"]) for x in snaps if x["cond"] == cn and minutes(x["t"]) <= 480]
    lines = ["t n", "0 0"] + [f"{m:.1f} {n}" for m, n in pts] + [f"480 {pts[-1][1]}"]
    (OUT / f"paper/data/cs7_curve_{cn}.dat").write_text("\n".join(lines) + "\n")
    M[f"CSsevenSnapOneMin{cn}"] = f"{pts[0][0]:.0f}"; M[f"CSsevenSnapOne{cn}"] = pts[0][1]
    M[f"CSsevenSnapTwoMin{cn}"] = f"{pts[1][0]:.0f}"; M[f"CSsevenSnapTwo{cn}"] = pts[1][1]
    last = max(i for i, (m, n) in enumerate(pts) if n < pts[-1][1]) + 1  # first snapshot showing the final count
    M[f"CSsevenFinalByMin{cn}"] = f"{pts[last][0]:.0f}"; M[f"CSsevenFinalAfterMin{cn}"] = f"{pts[last - 1][0]:.0f}"
# agent-reported first referee acceptance (ledger), supplementary
def ledger_first(cn):
    ts = []
    for l in (OUT / f"data/cs7_{cn}_ledger.jsonl").read_text().splitlines():
        if not l.strip():
            continue
        d = json.loads(l)
        if d.get("accepted") is True or d.get("status") == "accepted":
            t = str(d.get("ts"))
            if "T" in t:
                ts.append((datetime.fromisoformat(t[:19]).replace(tzinfo=timezone.utc).timestamp() - 3 * 3600 - START) / 60)
    return min(ts)
M["CSsevenLedgerFirstTS"] = f"{ledger_first('TS'):.0f}"; M["CSsevenLedgerFirstTW"] = f"{ledger_first('TW'):.0f}"
tw_ids = set(a["accepted"]["TW"])
# tokens
tok = D("token_account.json")


def tot(key):
    t = {"calls": 0, "input": 0, "cacheRead": 0, "output": 0}
    for m, v in tok[key]["by_model"].items():
        if m.startswith("zai/"):
            for f in t:
                t[f] += v.get(f, 0)
    return t


for cn in ("TS", "TW"):
    t = tot(f"CS7-{cn}"); k = len(a["accepted"][cn])
    M |= {f"CSseven{cn}Calls": num(t["calls"]), f"CSseven{cn}PromptM": f"{(t['input'] + t['cacheRead']) / 1e6:.1f}",
          f"CSseven{cn}OutM": f"{t['output'] / 1e6:.2f}", f"CSseven{cn}CallsPer": f"{t['calls'] / k:.0f}",
          f"CSseven{cn}PromptPerM": f"{(t['input'] + t['cacheRead']) / k / 1e6:.1f}", f"CSseven{cn}OutPerK": f"{t['output'] / k / 1e3:.0f}"}
ts_t, tw_t = tot("CS7-TS"), tot("CS7-TW")
M["CSsevenCallRatio"] = f"{tw_t['calls'] / ts_t['calls']:.1f}"
M["CSsevenOutRatio"] = f"{tw_t['output'] / ts_t['output']:.1f}"
M["CSsevenProofRatio"] = f"{len(a['accepted']['TW']) / len(a['accepted']['TS']):.1f}"
M["CSsevenExtraCallsPer"] = num((tw_t["calls"] - ts_t["calls"]) / max(h1["b_TW_only"], 1))
M["CSsevenExtraOutPerK"] = f"{(tw_t['output'] - ts_t['output']) / max(h1['b_TW_only'], 1) / 1e3:.0f}"
(OUT / "paper/data/cs7_tokens.dat").write_text(
    "cond calls promptM outM\n" + "\n".join(f"{cn} {t['calls']} {(t['input'] + t['cacheRead']) / 1e6:.1f} {t['output'] / 1e6:.2f}"
                                         for cn, t in (("TS", ts_t), ("TW", tw_t))) + "\n")
# team concurrency from the session files (subagent lifetimes)
AG = Path.home() / ".prime/agent"
root_tw = tok["CS7-TW"]["roots"][0]
iv = []
for f in glob.glob(str(AG / f"session-artifacts/{root_tw}/**/*.jsonl"), recursive=True):
    if f.endswith("semantic-edges.jsonl"):
        continue
    ts = []
    for line in open(f, errors="replace"):
        try:
            t = json.loads(line).get("timestamp")
        except Exception:
            continue
        if t:
            ts.append(datetime.fromisoformat(str(t)[:19]).replace(tzinfo=timezone.utc).timestamp())
    if ts:
        iv.append((min(ts), max(ts)))
T0, T1 = 1791835690, 1791835690 + 8 * 3600
ev = sorted([(s, 1) for s, e in iv] + [(e, -1) for s, e in iv])
cur = peak = 0; area = 0.0; last = T0
for t, d in ev:
    tt = min(max(t, T0), T1); area += cur * (tt - last); last = tt; cur += d; peak = max(peak, cur)
M |= {"CSsevenWorkers": len(iv), "CSsevenPeak": peak, "CSsevenMeanConc": f"{area / (T1 - T0):.1f}"}

# ---------------- provider quota (all GLM calls on this machine, 5 h before the CS7 quota stop) ----------------
qc = qp = 0
for f in glob.glob(str(AG / "sessions/*.jsonl")) + glob.glob(str(AG / "session-artifacts/**/*.jsonl"), recursive=True):
    if f.endswith("semantic-edges.jsonl"):
        continue
    for line in open(f, errors="replace"):
        if '"usage"' not in line or '"assistant"' not in line:
            continue
        try:
            d = json.loads(line)
        except Exception:
            continue
        m = d.get("message") or {}; u = m.get("usage") or {}
        t = str(d.get("timestamp", ""))[:19]
        if m.get("provider") == "zai" and "2026-10-12T19:07" <= t < "2026-10-13T00:07":
            qc += 1; qp += int(u.get("input") or 0) + int(u.get("cacheRead") or 0)
M |= {"QuotaCalls": num(qc), "QuotaPromptM": f"{qp / 1e6:.0f}"}
# watchdog interventions (CS7)
for cn in ("TS", "TW"):
    wl = (L / f"work/{cn}/watchdog.log").read_text()
    M[f"CSseven{cn}Aborts"] = wl.count("in-kernel; abort"); M[f"CSseven{cn}Kills"] = wl.count("terminating pid")

# ---------------- CS3 (GPU kernel engineering) ----------------
c1, c2 = D("cs3_C1_final_verdict.json"), D("cs3_C2_final_verdict.json")
hid = {c: json.loads((OUT / f"data/cs3_{c}_hidden.log").read_text().split("EXIT")[0].strip()) for c in ("C1", "C2")}
M |= {"CSthreeCOneVis": f"{c1['speedup_decode']:.3f}", "CSthreeCTwoVis": f"{c2['speedup_decode']:.3f}",
      "CSthreeCOneHid": f"{hid['C1']['speedup_hidden']:.3f}", "CSthreeCTwoHid": f"{hid['C2']['speedup_hidden']:.3f}"}
# ---------------- CS4 (extremal constructions) ----------------
for c in ("S1", "S2"):
    v = D(f"cs4_{c}_final_verdict.json")
    M[f"CSfour{c.replace('1', 'One').replace('2', 'Two')}Match"] = sum(bool(x.get("matches_record")) for x in v.values())
    M[f"CSfour{c.replace('1', 'One').replace('2', 'Two')}Valid"] = sum(bool(x.get("valid")) for x in v.values())
M["CSfourN"] = len(D("cs4_S1_final_verdict.json"))
# ---------------- CS5 (HorizonMath constructions) ----------------
EXCL = {"S2": {"keich-128": "E3", "ruler-10000": "E6"}}  # DEVIATIONS.md: contaminated / forbidden source
for c in ("S1", "S2", "S3"):
    v = D(f"cs5_{c}_final_verdict.json"); w = {"S1": "One", "S2": "Two", "S3": "Three"}[c]
    M[f"CSfive{w}Valid"] = sum(bool(x.get("valid")) for x in v.values())
    M[f"CSfive{w}Match"] = sum(bool(x.get("matches_record")) and k not in EXCL.get(c, {}) for k, x in v.items())
M["CSfiveN"] = len(D("cs5_S1_final_verdict.json"))
M["CSfiveKeichOne"] = f"{D('cs5_S1_final_verdict.json')['keich-128']['score']:.7f}"
# ---------------- tokens for all studies ----------------
for key, name in (("CS3-C1", "CSthreeCOne"), ("CS3-C2", "CSthreeCTwo"), ("CS4-S1", "CSfourSOne"), ("CS4-S2", "CSfourSTwo"),
                  ("CS5-S1", "CSfiveSOne"), ("CS5-S2", "CSfiveSTwo"), ("CS5-S3", "CSfiveSThree")):
    t = tot(key)
    M[f"{name}Calls"] = num(t["calls"]); M[f"{name}OutM"] = f"{t['output'] / 1e6:.2f}"
for a_, b_, n_ in (("CS3-C1", "CS3-C2", "CSthree"), ("CS4-S1", "CS4-S2", "CSfour"), ("CS5-S1", "CS5-S2", "CSfive"), ("CS7-TS", "CS7-TW", "CSseven")):
    M[f"{n_}OutRatioAll"] = f"{tot(b_)['output'] / tot(a_)['output']:.1f}"
# ---------------- CS6 (open conjectures) ----------------
o1 = D("cs6_O1_final_verdict.json")
M["CSsixOAccepted"] = sum(bool(v.get("accepted")) for v in o1.values()) if isinstance(o1, dict) else 0
M["CSsixON"] = len(o1)

# live agents while the quota was being consumed (TS 1 + TW orchestrator 1 + TW workers), start -> quota stop
QSTOP = datetime(2026, 10, 13, 0, 7, tzinfo=timezone.utc).timestamp()
cur = 0; area = 0.0; last = T0
for t, d in ev:
    tt = min(max(t, T0), QSTOP); area += cur * (tt - last); last = tt; cur += d
M["QuotaAgents"] = f"{2 + area / (QSTOP - T0):.1f}"
qh = (QSTOP - T0) / 3600; per_agent_h = qc / qh / (2 + area / (QSTOP - T0))
M["QuotaHours"] = f"{qh:.1f}"; M["QuotaPerAgentH"] = f"{per_agent_h:.0f}"; M["QuotaSixteenH"] = f"{qc / (16 * per_agent_h):.1f}"
# numbers that exist only in prose records (each with its source in data/transcribed.json)
for k, v in json.loads((OUT / "data/transcribed.json").read_text()).items():
    if not k.startswith("_"):
        M[k] = v["value"]

# ---------------- CS7 D8 sensitivity (TW-only proofs first seen after the read) ----------------
D8_IDS = {"OEIS-129365-conjecture1", "OEIS-237271-conjecture_5", "OEIS-237271-observation_carmichael",
          "WrittenOnTheWallII-GraphConjecture200-conjecture200"}
_tw_only = set(a["TW_only"])
def _sf(k, n):
    return sum(math.comb(n, j) for j in range(k, n + 1)) / 2 ** n if n else 1.0
_b_all = len(_tw_only - D8_IDS)
_b_fam = len(_tw_only - {x for x in D8_IDS if "237271" in x})
M |= {"DeightAfter": len(_tw_only & D8_IDS), "DeightBefore": _b_all,
      "DeightPworst": f"{_sf(_b_all, _b_all):.2f}", "DeightPfam": f"{_sf(_b_fam, _b_fam):.4f}".rstrip("0"), "DeightBfam": _b_fam}

# ---------------- CS8 (independent agents) and CS9 (replication) ----------------
c8, c9 = D("cs8_analysis.json"), D("cs9_analysis.json")
for c in ("IA1", "IA2", "IA3", "IA4"):
    M[f"CSeight{c.replace('IA', 'IA').replace('1', 'One').replace('2', 'Two').replace('3', 'Three').replace('4', 'Four')}"] = c8["per_agent"][c]
M |= {"CSeightUnion": c8["union"], "CSeightSum": c8["sum_of_agents"], "CSeightDup": c8["solved_by_2plus"],
      "CSeightAllFour": sum(1 for v in c8["multiplicity"].values() if v == 4),
      "CSeightKone": f"{c8['expected_union_k']['1']:.1f}", "CSeightKtwo": f"{c8['expected_union_k']['2']:.1f}",
      "CSeightKthree": f"{c8['expected_union_k']['3']:.1f}", "CSeightKfour": f"{c8['expected_union_k']['4']:.1f}",
      "CSeightPvsTS": f"{c8['C2_union_vs_TS7']['p_one_sided']:.4f}", "CSeightBvsTS": c8["C2_union_vs_TS7"]["b_union_only"],
      "CSeightTWonlyHit": len(c8["tw_only_cs7_in_union"]), "CSeightDeightHit": len(set(c8["tw_only_cs7_in_union"]) & D8_IDS),
      "CSeightVsTWp": f"{c8['union_vs_TW7']['p_two_sided']:.1f}",
      "CSeightTMlo": c9["token_matched_union_at_TW2_budget"]["union_low"], "CSeightTMhi": c9["token_matched_union_at_TW2_budget"]["union_high"]}
t9 = c9["tokens"]
M |= {"CSeightCalls": num(t9["IA_total"][0]), "CSeightOutM": f"{t9['IA_total'][1] / 1e6:.2f}",
      "CSnineTSCalls": num(t9["TS2"][0]), "CSnineTSOutM": f"{t9['TS2'][1] / 1e6:.2f}",
      "CSnineTWCalls": num(t9["TW2"][0]), "CSnineTWOutM": f"{t9['TW2'][1] / 1e6:.2f}",
      "CSnineOutRatio": f"{t9['TW2'][1] / t9['TS2'][1]:.1f}", "CSeightOverTW": f"{t9['IA_total'][1] / t9['TW7'][1]:.1f}"}
r1, pool, c1, c2 = c9["R1"], c9["pooled_CS7_CS9"], c9["C1_TW2_vs_union"], c9["C2_union_vs_TS2"]
M |= {"CSnineTS": c9["n"]["TS2"], "CSnineTW": c9["n"]["TW2"], "CSnineB": r1["b_TW2_only"], "CSnineC": r1["c_TS2_only"],
      "CSnineP": f"{r1['p_one_sided']:.2f}", "CSnineTangoLo": f"{r1['tango'][0]:.1f}", "CSnineTangoHi": f"{r1['tango'][1]:.1f}",
      "PoolB": pool["b"], "PoolC": pool["c"], "PoolP": f"{pool['p_one_sided']:.4f}",
      "PoolSensB": pool["sensitivity_D8_removed"]["b"], "PoolSensP": f"{pool['sensitivity_D8_removed']['p_one_sided']:.4f}".rstrip("0"),
      "CoordB": c1["b_TW2_only"], "CoordC": c1["c_union_only"], "CoordP": f"{c1['p_two_sided']:.3f}",
      "CoordLo": f"{c1['tango_TW2_minus_union'][0]:.1f}", "CoordHi": f"{c1['tango_TW2_minus_union'][1]:.1f}",
      "CoordTWsevenP": f"{c9['C1_secondary_TW7_vs_union']['p_two_sided']:.1f}",
      "CoordTWsevenLo": f"{c9['C1_secondary_TW7_vs_union']['tango'][0]:.1f}", "CoordTWsevenHi": f"{c9['C1_secondary_TW7_vs_union']['tango'][1]:.1f}",
      "CtwoB": c2["b_union_only"], "CtwoP": f"{c2['p_one_sided']:.3f}"}
singles = [len(a["accepted"]["TS"])] + [c8["per_agent"][c] for c in ("IA1", "IA2", "IA3", "IA4")] + [c9["n"]["TS2"]]
M |= {"SingleRuns": len(singles), "SingleMean": f"{sum(singles) / len(singles):.1f}", "SingleMin": min(singles), "SingleMax": max(singles)}
# coverage vs output tokens (one point per condition)
pts = [("TS (CS7)", t9["TS7"][1], len(a["accepted"]["TS"]), "single"), ("TW (CS7)", t9["TW7"][1], len(a["accepted"]["TW"]), "team"),
       ("TS2 (CS9)", t9["TS2"][1], c9["n"]["TS2"], "single"), ("TW2 (CS9)", t9["TW2"][1], c9["n"]["TW2"], "team"),
       ("IA union (CS8)", t9["IA_total"][1], c8["union"], "union")]
tokc = D("token_account.json")
for c in ("IA1", "IA2", "IA3", "IA4"):
    o = sum(v.get("output", 0) for v in tokc[f"CS8-{c}"]["by_model"].values())
    pts.append((c, o, c8["per_agent"][c], "single"))
for kind in ("single", "team", "union"):
    (OUT / f"paper/data/cov_{kind}.dat").write_text("x y\n" + "\n".join(f"{o / 1e6:.3f} {n}" for _, o, n, k in pts if k == kind) + "\n")
# time curves of all conditions (hourly referee snapshots; minutes since each run's start)
starts = {"TS2": 1791951101, "TW2": 1791951101}
for cn, rows in c9["curve"].items():
    lines = ["t n"] + ([] if cn == "TW2" else ["0 0"])  # TW2's snapshots before 09:12 are invalid (D10): no fake zero
    for hhmm, n in rows:
        hh, mm = map(int, hhmm.split(":")); t = (hh * 60 + mm) - (7 * 60 + 11)
        if 0 < t <= 480:
            lines.append(f"{t} {n}")
    if not lines[-1].startswith("480 "):
        lines.append(f"480 {rows[-1][1]}")
    (OUT / f"paper/data/cs9_curve_{cn}.dat").write_text("\n".join(lines) + "\n")
lines = ["t n", "0 0"]
for hh, n in c8["union_curve_by_hour"].items():
    h = int(hh[11:13]) + (24 if hh[8:10] == "14" else 0); t = (h * 60 + 12) - (17 * 60 + 43)
    if 0 < t <= 480:
        lines.append(f"{t} {n}")
lines.append(f"480 {c8['union']}")
(OUT / "paper/data/cs8_curve_union.dat").write_text("\n".join(lines) + "\n")

body = "% generated by scripts/build_data.py -- do not edit\n" + "".join(
    f"\\newcommand{{\\{k}}}{{{v}}}\n" for k, v in sorted(M.items()))
(OUT / "paper/numbers.tex").write_text(body)
print(f"{len(M)} macros -> paper/numbers.tex")
for k in sorted(M):
    print(f"  {k} = {M[k]}")
