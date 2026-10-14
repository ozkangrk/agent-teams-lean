#!/usr/bin/env python3
"""Pre-registered CS8 analysis (Claude's code; PREREG_CS8_CS9.md). Four independent single agents IA1-IA4.

    analyze_cs8.py            prints the analysis and writes conditions/cs8_analysis.json

Union of referee-accepted statements over IA1-IA4 (Claude's final re-run); per-agent counts; expected union size
for k = 1..4 (mean over all k-subsets); duplication; C2 (union > CS7 TS, one-sided exact McNemar); union vs CS7 TW
(two-sided exact McNemar + Tango CI; CS7 TW carries the D8 caveat); token-matched union (proofs present at the last
snapshot before the four agents' cumulative GLM output tokens reached a reference total); union over time.
The primary coordination test (C1: TW2 vs union) is run in analyze_cs9.py.
"""
import glob, itertools, json, math
from datetime import datetime, timezone
from pathlib import Path

P = Path(__file__).resolve().parent.parent
C = P / "conditions"
IA = ["IA1", "IA2", "IA3", "IA4"]
probs = [json.loads(l) for l in (C / "cs7_set.jsonl").read_text().splitlines() if l.strip()]
ids = [p["id"] for p in probs]
acc = {c: {i for i, v in json.loads((P / f"work/{c}/final_verdict.json").read_text()).items() if v.get("accepted")} for c in IA}
union = set().union(*acc.values())
cs7 = json.loads((C / "cs7_analysis.json").read_text())
TS, TW = set(cs7["accepted"]["TS"]), set(cs7["accepted"]["TW"])


def binom_sf(k, n):
    return sum(math.comb(n, j) for j in range(k, n + 1)) / 2 ** n if n else 1.0


def mcnemar_two_sided(b, c):
    n = b + c
    if n == 0:
        return 1.0
    k = max(b, c)
    return min(1.0, 2 * binom_sf(k, n))


def tango(b, c, n, z=1.959964):
    def stat(d):
        A, B, Cc = 2 * n, -b - c + (2 * n - b + c) * d, -c * d * (1 - d)
        q = (math.sqrt(max(B * B - 4 * A * Cc, 0)) - B) / (2 * A)
        v = n * (2 * q + d * (1 - d))
        return (b - c - n * d) / math.sqrt(v) if v > 0 else float("inf")
    inside = [d / 10000 for d in range(-9999, 10000) if abs(stat(d / 10000)) <= z]
    return min(inside), max(inside)


N = len(ids)
# expected union for k-subsets
exp_union = {k: sum(len(set().union(*(acc[c] for c in s))) for s in itertools.combinations(IA, k)) / math.comb(4, k) for k in range(1, 5)}
mult = {i: sum(i in acc[c] for c in IA) for i in union}
dup = sum(1 for v in mult.values() if v >= 2)
# C2: union vs CS7 TS (one-sided union > TS)
b_ts, c_ts = len(union - TS), len(TS - union)
# union vs CS7 TW (two-sided)
b_tw, c_tw = len(TW - union), len(union - TW)

# cumulative GLM output tokens over time across the four sessions
events = []
for c in IA:
    d = P / f"agent-sessions/{c}"
    for f in glob.glob(str(d / "sessions/*.jsonl")) + [x for x in glob.glob(str(d / "session-artifacts/**/*.jsonl"), recursive=True) if not x.endswith("semantic-edges.jsonl")]:
        for line in open(f, errors="replace"):
            if '"usage"' not in line:
                continue
            try:
                e = json.loads(line)
            except Exception:
                continue
            m = e.get("message") or {}
            if m.get("role") == "assistant" and m.get("usage") and str(m.get("provider")) == "zai":
                t = datetime.fromisoformat(str(e["timestamp"])[:19]).replace(tzinfo=timezone.utc).timestamp()
                events.append((t, int(m["usage"].get("output") or 0)))
events.sort()
snaps = [json.loads(l) for l in (C / "snapshots.jsonl").read_text().splitlines() if '"cond": "IA' in l]


def snap_union_before(t_epoch):
    best = {}
    for s in snaps:
        ts = datetime.fromisoformat(s["t"]).replace(tzinfo=timezone.utc).timestamp() - 3 * 3600  # local +03 -> UTC
        if ts <= t_epoch:
            best[s["cond"]] = set(s["accepted"])  # snapshots are appended in time order
    return set().union(*best.values()) if best else set()


def token_matched(ref_out):
    cum = 0
    for t, o in events:
        cum += o
        if cum >= ref_out:
            return t, snap_union_before(t)
    return None, union  # never reached: the whole run is within budget


tot_out = sum(o for _, o in events)
tok = json.loads((C / "token_account.json").read_text())
ref = {k: sum(v.get("output", 0) for v in tok[k]["by_model"].values()) for k in ("CS7-TS", "CS7-TW")}
tm = {}
for k, r in ref.items():
    t, u = token_matched(r)
    tm[k] = {"ref_output": r, "reached_at_utc": datetime.fromtimestamp(t, timezone.utc).isoformat()[:19] if t else None,
             "union_at_budget": len(u), "ids": sorted(u)}
# union over time (hourly snapshot groups)
curve = {}
for s in snaps:
    key = s["t"][:13]
    curve.setdefault(key, {})[s["cond"]] = set(s["accepted"])
curve = {k: len(set().union(*v.values())) for k, v in sorted(curve.items())}

out = {
    "N": N, "per_agent": {c: len(acc[c]) for c in IA}, "per_agent_ids": {c: sorted(acc[c]) for c in IA},
    "union": len(union), "union_ids": sorted(union), "sum_of_agents": sum(len(acc[c]) for c in IA),
    "expected_union_k": exp_union, "solved_by_2plus": dup, "multiplicity": mult,
    "new_vs_cs7": sorted(union - TS - TW), "tw_only_cs7_in_union": sorted(union & set(cs7["TW_only"])),
    "C2_union_vs_TS7": {"b_union_only": b_ts, "c_TS_only": c_ts, "p_one_sided": binom_sf(b_ts, b_ts + c_ts)},
    "union_vs_TW7": {"b_TW_only": b_tw, "c_union_only": c_tw, "p_two_sided": mcnemar_two_sided(b_tw, c_tw),
                     "tango_CI95_TW_minus_union": tango(b_tw, c_tw, N), "note": "CS7 TW has the D8 caveat"},
    "tokens_output_total": tot_out, "token_matched": tm, "union_curve_by_hour": curve,
}
(C / "cs8_analysis.json").write_text(json.dumps(out, indent=1, ensure_ascii=False))
print(f"per agent {out['per_agent']}  sum {out['sum_of_agents']}  union {len(union)}  solved by >=2: {dup}")
print("expected union k=1..4:", {k: round(v, 2) for k, v in exp_union.items()})
print("new vs CS7:", out["new_vs_cs7"], "| CS7 TW-only in union:", out["tw_only_cs7_in_union"])
print("C2 union vs CS7 TS:", out["C2_union_vs_TS7"])
print("union vs CS7 TW:", out["union_vs_TW7"])
print(f"IA output tokens {tot_out / 1e6:.2f}M;", {k: (v["union_at_budget"], v["reached_at_utc"]) for k, v in tm.items()})
print("union curve:", curve)
