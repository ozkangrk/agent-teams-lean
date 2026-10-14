#!/usr/bin/env python3
"""Referee self-test (Claude's code): valid examples, known-invalid examples, exploit attempts, independent cross-checks.
Run: referee/.venv/bin/python -I referee/selftest.py"""
import itertools, json, math, random, sys, tempfile, time
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import verify as V  # noqa: E402

R = V.RECORDS
ok = True


def check(name, cond, info=""):
    global ok
    ok &= bool(cond)
    print(("PASS " if cond else "FAIL ") + name + (f"  [{info}]" if info else ""))


rng = random.Random(1)

# heilbronn: valid, out-of-square exploit, collinear
pts = [[rng.random(), rng.random()] for _ in range(12)]
v = V.heilbronn({"points": pts}, R["heilbronn-12"]); check("heilbronn valid", v["valid"], v.get("score"))
check("heilbronn rejects 1e-12 outside", not V.heilbronn({"points": [[1 + 1e-12, 0.5]] + pts[1:]}, R["heilbronn-12"])["valid"])
check("heilbronn rejects collinear", not V.heilbronn({"points": [[0, 0], [0.5, 0.5], [1, 1]] + pts[3:]}, R["heilbronn-12"])["valid"])
check("heilbronn rejects bool/str", not V.heilbronn({"points": [["0.1", 0.2]] + pts[1:]}, R["heilbronn-12"])["valid"])

# tammes: radial scaling must not change the score; icosahedron-like sanity
P = np.random.default_rng(2).normal(size=(15, 3)); P /= np.linalg.norm(P, axis=1)[:, None]
a = V.tammes({"points": P.tolist()}, R["tammes-15"]); b = V.tammes({"points": (P * (1 + 9e-7)).tolist()}, R["tammes-15"])
check("tammes valid", a["valid"], a.get("score")); check("tammes scale-invariant (no slack exploit)", abs(a["score"] - b["score"]) < 1e-12)
check("tammes rejects far-off-sphere", not V.tammes({"points": (P * 1.01).tolist()}, R["tammes-15"])["valid"])

# keich: independent fine-grid estimate vs exact-crossing computation
bb = [rng.uniform(-0.6, 0.1) for _ in range(128)]
t0 = time.time(); k = V.keich({"intercepts": bb}, R["keich-128"]); tk = time.time() - t0
a_ = np.arange(128) / 128; d = 1 / 128
xs = np.linspace(0, 1, 40001); L = []
for x in xs:
    top = a_ * x + np.asarray(bb); bot = top - d * (1 - x); o = np.argsort(bot); top, bot = top[o], bot[o]
    tot, cur = 0.0, -np.inf
    for lo, hi in zip(bot, top):
        tot += max(0.0, hi - max(lo, cur)); cur = max(cur, hi)
    L.append(tot)
grid = np.trapezoid(L, xs)
check("keich valid", k["valid"], f"{k['score']:.12f} in {tk:.1f}s")
check("keich agrees with grid estimate (1e-6)", abs(k["score"] - grid) < 1e-6, f"grid {grid:.12f}")
# all-zero intercepts: a fan; independent closed check via grid too
check("keich rejects |b|>4", not V.keich({"intercepts": [5.0] + bb[1:]}, R["keich-128"])["valid"])
check("keich rejects nan", not V.keich({"intercepts": [float("nan")] + bb[1:]}, R["keich-128"])["valid"])

# autocorrelation: constant function has ratio exactly 2; scale exploit; negative rejected
check("autocorr constant = 2", abs(V.autocorr({"heights": [1.0] * 1000}, R["autocorr-c1"])["score"] - 2) < 1e-12)
h = list(np.random.default_rng(3).random(500))
s1 = V.autocorr({"heights": h}, R["autocorr-c1"])["score"]; s2 = V.autocorr({"heights": [x * 1e-160 for x in h]}, R["autocorr-c1"])["score"]
check("autocorr scale-invariant (1e-160 trick)", abs(s1 - s2) < 1e-12 * s1, f"{s1:.9f} vs {s2:.9f}")
check("autocorr rejects negative", not V.autocorr({"heights": [-1.0] + h[1:]}, R["autocorr-c1"])["valid"])
check("autocorr rejects too long", not V.autocorr({"heights": [1.0] * 100001}, R["autocorr-c1"])["valid"])
t0 = time.time(); V.autocorr({"heights": list(np.random.default_rng(4).random(100000))}, R["autocorr-c1"]); check("autocorr n=100000 time", True, f"{time.time() - t0:.1f}s")

# dts: greedy valid (7,5) set; repeated difference rejected; float rejected
seen, rows = set(), []
for _ in range(7):
    row = [0]
    while len(row) < 6:
        c = row[-1] + 1
        while True:
            ds = {c - x for x in row}
            if not (ds & seen) and len(ds) == len(row):
                break
            c += 1
        seen |= {c - x for x in row}; row.append(c)
    rows.append(row)
v = V.dts({"rows": rows}, R["dts-7-5"]); check("dts greedy valid", v["valid"], v.get("score"))
bad_rows = [r[:] for r in rows]; bad_rows[1] = rows[0][:]
check("dts rejects repeated difference", not V.dts({"rows": bad_rows}, R["dts-7-5"])["valid"])
fl = [r[:] for r in rows]; fl[0][1] = float(fl[0][1])
check("dts rejects float entries", not V.dts({"rows": fl}, R["dts-7-5"])["valid"])

# vdw: brute-force cross-check on random colourings
for trial in range(3):
    n = 300; col = [rng.randint(0, 1) for _ in range(n)]
    brute = all(len({col[a + t * dd] for t in range(7)}) > 1 for dd in range(1, n) for a in range(n - 6 * dd))
    check(f"vdw agrees with brute force #{trial}", V.vdw({"coloring": col}, R["vdw-2-7"])["valid"] == brute)
check("vdw rejects all-zero length 7", not V.vdw({"coloring": [0] * 7}, R["vdw-2-7"])["valid"])
check("vdw rejects bool", not V.vdw({"coloring": [True, False] * 5}, R["vdw-2-7"])["valid"])
col = [0, 1] * 1850 + [0, 1, 1]
t0 = time.time(); V.vdw({"coloring": col}, R["vdw-2-7"]); check("vdw n=3703 time", True, f"{time.time() - t0:.2f}s")

# packing / covering: greedy constructions; violation detection
B = []
for b in itertools.combinations(range(29), 5):
    if all(len(set(b) & set(c)) <= 1 for c in B):
        B.append(b)
v = V.packing_pairs({"blocks": [list(b) for b in B]}, R["cwcode-29-8-5"]); check("packing greedy valid", v["valid"], v.get("score"))
check("packing rejects shared pair", not V.packing_pairs({"blocks": [list(B[0]), [B[0][0], B[0][1], 27, 26, 25]]}, R["cwcode-29-8-5"])["valid"])
cov = []
for t in itertools.combinations(range(13), 4):
    if not any(set(t) <= set(c) for c in cov):
        cov.append(sorted(set(t) | set(rng.sample([x for x in range(13) if x not in t], 3))))
v = V.covering({"blocks": cov}, R["covering-13-7-4"]); check("covering greedy valid", v["valid"], v.get("score"))
check("covering rejects incomplete", not V.covering({"blocks": cov[:-1]}, R["covering-13-7-4"])["valid"] or len(cov) < 2)

# linear code: brute-force min distance on a small random code via the same Gray walk vs direct enumeration
G = ["".join(rng.choice("01") for _ in range(68)) for _ in range(15)]
v = V.linear_code({"generator_matrix": G}, R["bklc-68-15"])
rows_ = [int(r, 2) for r in G]
direct = min(bin(np.bitwise_xor.reduce([rows_[i] for i in range(15) if m >> i & 1])).count("1") for m in range(1, 1 << 15)) if v["valid"] else None
check("linear code d matches direct enumeration", v["valid"] and v["score"] == direct, f"d={v.get('score')}")
check("linear code rejects rank-deficient", not V.linear_code({"generator_matrix": [G[0]] * 15}, R["bklc-68-15"])["valid"])

# difference basis: explicit valid basis of size 199; removing one element breaks it
basis = list(range(100)) + [100 * j + 99 for j in range(1, 100)]
v = V.difference_basis({"basis": basis}, R["ruler-10000"]); check("ruler valid (199)", v["valid"] and v["score"] == 199)
check("ruler rejects missing difference", not V.difference_basis({"basis": basis[:-1]}, R["ruler-10000"])["valid"])

# end-to-end CLI on a directory + record comparison logic
with tempfile.TemporaryDirectory() as td:
    Path(td, "ruler-10000.json").write_text(json.dumps({"basis": basis}))
    Path(td, "dts-7-5.json").write_text("not json")
    import subprocess
    r = subprocess.run([sys.executable, "-I", str(HERE / "verify.py"), td], capture_output=True, text=True)
    out = json.loads(r.stdout)
    check("cli: ruler gap computed", out["ruler-10000"]["valid"] and out["ruler-10000"]["matches_record"] is False)
    check("cli: malformed file handled", out["dts-7-5"]["valid"] is False)
print("ALL PASS" if ok else "SOME FAILED")
sys.exit(0 if ok else 1)
