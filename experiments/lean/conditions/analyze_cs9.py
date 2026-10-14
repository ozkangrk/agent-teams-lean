#!/usr/bin/env python3
"""Pre-registered CS9 analysis and the CS7/CS8/CS9 combination (Claude's code; PREREG_CS8_CS9.md).

    analyze_cs9.py            prints the analysis and writes conditions/cs9_analysis.json

R1  replication: TW2 > TS2, exact one-sided McNemar.
    Pooled CS7+CS9 (one-sided binomial on b7+b9 vs c7+c9), and a sensitivity analysis with CS7's four D8-affected
    TW-only proofs removed.
C1  coordination (primary): TW2 vs IA-union (CS8), two-sided exact McNemar + Tango 95% CI; secondary vs CS7 TW.
C2  parallelism: IA-union > TS2 (one-sided).
Token-matched: IA-union at TW2's total GLM output tokens (from cs8_analysis machinery: last snapshot before the four
agents' cumulative output reached the budget).
"""
import glob, json, math
from datetime import datetime, timezone
from pathlib import Path

P = Path(__file__).resolve().parent.parent
C = P / "conditions"
probs = [json.loads(l) for l in (C / "cs7_set.jsonl").read_text().splitlines() if l.strip()]
N = len(probs)
fin = lambda c: {i for i, v in json.loads((P / f"work/{c}/final_verdict.json").read_text()).items() if v.get("accepted")}
TS2, TW2 = fin("TS2"), fin("TW2")
cs7 = json.loads((C / "cs7_analysis.json").read_text()); cs8 = json.loads((C / "cs8_analysis.json").read_text())
TS7, TW7 = set(cs7["accepted"]["TS"]), set(cs7["accepted"]["TW"])
U = set(cs8["union_ids"])
D8 = {"OEIS-129365-conjecture1", "OEIS-237271-conjecture_5", "OEIS-237271-observation_carmichael",
      "WrittenOnTheWallII-GraphConjecture200-conjecture200"}  # CS7 TW-only proofs first seen after the D8 read


def sf(k, n):
    return sum(math.comb(n, j) for j in range(k, n + 1)) / 2 ** n if n else 1.0


def two_sided(b, c):
    return min(1.0, 2 * sf(max(b, c), b + c)) if b + c else 1.0


def tango(b, c, n=N, z=1.959964):
    def stat(d):
        A, B, Cc = 2 * n, -b - c + (2 * n - b + c) * d, -c * d * (1 - d)
        q = (math.sqrt(max(B * B - 4 * A * Cc, 0)) - B) / (2 * A)
        v = n * (2 * q + d * (1 - d))
        return (b - c - n * d) / math.sqrt(v) if v > 0 else float("inf")
    inside = [d / 10000 for d in range(-9999, 10000) if abs(stat(d / 10000)) <= z]
    return round(min(inside) * 100, 1), round(max(inside) * 100, 1)


def pair(x, y):  # b = only in x, c = only in y
    return len(x - y), len(y - x)


out = {"N": N, "TS2": sorted(TS2), "TW2": sorted(TW2), "n": {"TS2": len(TS2), "TW2": len(TW2)}}
b9, c9 = pair(TW2, TS2)
b7, c7 = pair(TW7, TS7)
b7s, c7s = pair(TW7 - D8, TS7)
out["R1"] = {"b_TW2_only": b9, "c_TS2_only": c9, "p_one_sided": sf(b9, b9 + c9), "diff_pts": b9 - c9, "tango": tango(b9, c9),
             "TW2_only": sorted(TW2 - TS2), "TS2_only": sorted(TS2 - TW2)}
out["pooled_CS7_CS9"] = {"b": b7 + b9, "c": c7 + c9, "p_one_sided": sf(b7 + b9, b7 + b9 + c7 + c9),
                         "sensitivity_D8_removed": {"b": b7s + b9, "c": c7s + c9, "p_one_sided": sf(b7s + b9, b7s + b9 + c7s + c9)}}
bt, ct = pair(TW2, U)
out["C1_TW2_vs_union"] = {"b_TW2_only": bt, "c_union_only": ct, "p_two_sided": two_sided(bt, ct), "diff_pts": bt - ct,
                          "tango_TW2_minus_union": tango(bt, ct), "TW2_only": sorted(TW2 - U), "union_only": sorted(U - TW2)}
bt7, ct7 = pair(TW7, U)
out["C1_secondary_TW7_vs_union"] = {"b": bt7, "c": ct7, "p_two_sided": two_sided(bt7, ct7), "tango": tango(bt7, ct7)}
bu, cu = pair(U, TS2)
out["C2_union_vs_TS2"] = {"b_union_only": bu, "c_TS2_only": cu, "p_one_sided": sf(bu, bu + cu)}
out["C2_union_vs_TS7"] = cs8["C2_union_vs_TS7"]
# tokens
tok = json.loads((C / "token_account.json").read_text())
outk = lambda k: sum(v.get("output", 0) for v in tok[k]["by_model"].values())
calls = lambda k: sum(v.get("calls", 0) for v in tok[k]["by_model"].values())
ia_out = sum(outk(k) for k in tok if k.startswith("CS8-")); ia_calls = sum(calls(k) for k in tok if k.startswith("CS8-"))
out["tokens"] = {"TS7": [calls("CS7-TS"), outk("CS7-TS")], "TW7": [calls("CS7-TW"), outk("CS7-TW")],
                 "IA_total": [ia_calls, ia_out], "TS2": [calls("CS9-TS2"), outk("CS9-TS2")], "TW2": [calls("CS9-TW2"), outk("CS9-TW2")]}
# token-matched union at TW2's budget: reuse the CS8 event stream
events = []
for c in ["IA1", "IA2", "IA3", "IA4"]:
    d = P / f"agent-sessions/{c}"
    for f in glob.glob(str(d / "sessions/*.jsonl")):
        for line in open(f, errors="replace"):
            if '"usage"' not in line:
                continue
            try:
                e = json.loads(line)
            except Exception:
                continue
            m = e.get("message") or {}
            if m.get("role") == "assistant" and m.get("usage") and str(m.get("provider")) == "zai":
                events.append((datetime.fromisoformat(str(e["timestamp"])[:19]).replace(tzinfo=timezone.utc).timestamp(), int(m["usage"].get("output") or 0)))
events.sort()
snaps = [json.loads(l) for l in (C / "snapshots.jsonl").read_text().splitlines() if '"cond": "IA' in l]


def union_at_budget(ref):
    cum, t_hit = 0, None
    for t, o in events:
        cum += o
        if cum >= ref:
            t_hit = t; break
    if t_hit is None:
        return None, len(U), len(U)
    before, after = {}, {}
    for s in snaps:
        ts = datetime.fromisoformat(s["t"]).replace(tzinfo=timezone.utc).timestamp() - 3 * 3600
        (before if ts <= t_hit else after).setdefault(s["cond"], []).append(set(s["accepted"]))
    lo = len(set().union(*[v[-1] for v in before.values()])) if before else 0
    hi = len(set().union(*[v[0] for v in after.values()])) if after else len(U)
    return datetime.fromtimestamp(t_hit, timezone.utc).isoformat()[:19], lo, hi


t, lo, hi = union_at_budget(outk("CS9-TW2"))
out["token_matched_union_at_TW2_budget"] = {"budget_output": outk("CS9-TW2"), "reached_utc": t, "union_low": lo, "union_high": hi}
# snapshots over time (CS9; TW2 rows before 09:12 are invalid, D10)
cur = {}
for l in (C / "snapshots.jsonl").read_text().splitlines():
    if '"cond": "T' in l and ('"TS2"' in l or '"TW2"' in l):
        s = json.loads(l)
        if s["cond"] == "TW2" and s["t"] < "2026-10-14T09:12":
            continue
        cur.setdefault(s["cond"], []).append((s["t"][11:16], s["n_accepted"]))
out["curve"] = cur
out["new_statements_any_run"] = sorted((TS2 | TW2 | U) - TS7 - TW7)
(C / "cs9_analysis.json").write_text(json.dumps(out, indent=1, ensure_ascii=False))
for k in ("n", "R1", "pooled_CS7_CS9", "C1_TW2_vs_union", "C1_secondary_TW7_vs_union", "C2_union_vs_TS2", "tokens",
          "token_matched_union_at_TW2_budget", "curve", "new_statements_any_run"):
    print(k, "=", json.dumps(out[k], ensure_ascii=False))
