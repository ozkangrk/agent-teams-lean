#!/usr/bin/env python3
"""Pre-registered CS7 analysis (Claude's code; PREREG_CS7.md + A1 + A2).

    analyze_cs7.py            prints the analysis and writes conditions/cs7_analysis.json

H1 exact one-sided McNemar on discordant pairs (b = TW-only, c = TS-only), paired difference with an exact 95 % CI
(conditional Clopper-Pearson on the discordant split, transformed to the difference scale) and Tango's score CI as an
unconditional sensitivity check; plus a cluster-level sensitivity test (one unit per upstream source file, because
the sampler allowed up to 2 statements per file). H2 time curve (hourly referee snapshots + proof-file birth times),
H3 tokens per accepted proof, H5 overlap, H6 solve rate by resolution month. H4 is read from the scans in DEVIATIONS.
"""
import json, math, os
from pathlib import Path

P = Path(__file__).resolve().parent.parent
C = P / "conditions"
probs = [json.loads(l) for l in (C / "cs7_set.jsonl").read_text().splitlines() if l.strip()]
ids = [p["id"] for p in probs]
fin = {c: json.loads((P / f"work/{c}/final_verdict.json").read_text()) for c in ("TS", "TW")}
acc = {c: {i for i in ids if fin[c][i].get("accepted")} for c in fin}
N = len(ids)
both, tw_only, ts_only = acc["TS"] & acc["TW"], acc["TW"] - acc["TS"], acc["TS"] - acc["TW"]
b, c = len(tw_only), len(ts_only)


def binom_sf(k, n):  # P(X >= k), X ~ Bin(n, 1/2)
    return sum(math.comb(n, j) for j in range(k, n + 1)) / 2 ** n


def beta_ppf(q, a, bb):  # Clopper-Pearson bound by bisection on the binomial cdf
    lo, hi = 0.0, 1.0
    for _ in range(200):
        m = (lo + hi) / 2
        # regularized incomplete beta via binomial sum: I_m(a, bb) = P(Bin(a+bb-1, m) >= a)
        n = a + bb - 1
        v = sum(math.comb(n, j) * m ** j * (1 - m) ** (n - j) for j in range(a, n + 1))
        lo, hi = (m, hi) if v < q else (lo, m)
    return (lo + hi) / 2


def cp(k, n, alpha=0.05):
    lo = 0.0 if k == 0 else beta_ppf(alpha / 2, k, n - k + 1)
    hi = 1.0 if k == n else beta_ppf(1 - alpha / 2, k + 1, n - k)
    return lo, hi


def tango(b, c, n, z=1.959964):
    def stat(d):
        A, B, Cc = 2 * n, -b - c + (2 * n - b + c) * d, -c * d * (1 - d)
        q = (math.sqrt(max(B * B - 4 * A * Cc, 0)) - B) / (2 * A)
        v = n * (2 * q + d * (1 - d))
        return (b - c - n * d) / math.sqrt(v) if v > 0 else float("inf")
    grid = [i / 10000 for i in range(-9999, 10000)]
    inside = [d for d in grid if abs(stat(d)) <= z]
    return min(inside), max(inside)


nd = b + c
p1 = binom_sf(b, nd) if nd else 1.0
plo, phi = cp(b, nd) if nd else (0, 1)
diff = (b - c) / N
cond_ci = (nd / N * (2 * plo - 1), nd / N * (2 * phi - 1))
tl, th = tango(b, c, N)

# cluster sensitivity: one unit per upstream file (solved by a condition if any of its statements is)
files = sorted({p["file"] for p in probs})
fs = {cn: {p["file"] for p in probs if p["id"] in acc[cn]} for cn in acc}
fb, fc = len(fs["TW"] - fs["TS"]), len(fs["TS"] - fs["TW"])
pf = binom_sf(fb, fb + fc) if fb + fc else 1.0

# H2: hourly referee snapshots + proof-file birth times (first time a referee-accepted file existed)
snaps = [json.loads(l) for l in (C / "snapshots.jsonl").read_text().splitlines() if '"cond": "T' in l]
curve = {cn: [(s["t"], s["n_accepted"]) for s in snaps if s["cond"] == cn] for cn in acc}
START = 1791835690  # 2026-10-12 23:08:10 +03
birth = {}
for cn in acc:
    birth[cn] = {}
    for i in acc[cn]:
        f = P / f"work/{cn}/proofs" / fin[cn][i]["file"]
        st = os.stat(f)
        t = getattr(st, "st_birthtime", None)
        if t is None:  # Linux: statx birth time through `stat -c %W`
            t = int(os.popen(f"stat -c %W '{f}'").read().strip() or 0) or st.st_mtime
        birth[cn][i] = round((t - START) / 60, 1)

# H3 tokens
tok = json.loads((C / "token_account.json").read_text())
h3 = {}
for cn in acc:
    m = tok[f"CS7-{cn}"]["by_model"]
    t = {k: sum(v.get(k, 0) for v in m.values()) for k in ("calls", "input", "cacheRead", "output")}
    k = len(acc[cn])
    h3[cn] = {**t, "accepted": k, "calls_per_proof": round(t["calls"] / k, 1),
              "prompt_tokens_per_proof_M": round((t["input"] + t["cacheRead"]) / k / 1e6, 2),
              "output_tokens_per_proof_k": round(t["output"] / k / 1e3, 1)}

# H6 by resolution month
months = sorted({p["solved_date"][:7] for p in probs})
h6 = {m: {"n": sum(p["solved_date"].startswith(m) for p in probs),
          **{cn: sum(p["solved_date"].startswith(m) and p["id"] in acc[cn] for p in probs) for cn in acc}} for m in months}
src = {}
for p in probs:
    s = p["file"].split("/")[1]
    src.setdefault(s, {"n": 0, "TS": 0, "TW": 0}); src[s]["n"] += 1
    for cn in acc:
        src[s][cn] += p["id"] in acc[cn]

out = {"N": N, "accepted": {cn: sorted(acc[cn]) for cn in acc}, "both": sorted(both), "TW_only": sorted(tw_only),
       "TS_only": sorted(ts_only), "H1": {"b_TW_only": b, "c_TS_only": c, "p_one_sided": p1, "diff": diff,
       "exact_conditional_CI95": cond_ci, "tango_CI95": (tl, th),
       "cluster_files": {"n_files": len(files), "TW_only": fb, "TS_only": fc, "p_one_sided": pf}},
       "H2": {"snapshots": curve, "minutes_to_first_file": birth}, "H3": h3, "H6": h6, "by_source": src}
(C / "cs7_analysis.json").write_text(json.dumps(out, indent=1, ensure_ascii=False))
print(f"N={N}  TS={len(acc['TS'])}  TW={len(acc['TW'])}  both={len(both)}  TW-only={b}  TS-only={c}")
print(f"H1 one-sided exact McNemar p={p1:.4f}; diff={diff * 100:+.1f} pts; exact conditional 95% CI "
      f"[{cond_ci[0] * 100:.1f}, {cond_ci[1] * 100:.1f}]; Tango 95% CI [{tl * 100:.1f}, {th * 100:.1f}]")
print(f"   cluster (files, n={len(files)}): TW-only={fb} TS-only={fc} p={pf:.4f}")
print("   TW-only:", sorted(tw_only))
for cn in acc:
    ts = sorted(birth[cn].values())
    print(f"H2 {cn}: proof files created at minutes {ts}")
for cn in acc:
    print(f"H3 {cn}: {h3[cn]}")
print("H6:", h6)
print("by source:", src)
