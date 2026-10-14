#!/usr/bin/env python3
"""CS5 referee (Claude's code, written independently from the HorizonMath problem statements; agents must never edit
referee/). Verifies solutions/<instance>.json files.

    verify.py SOLUTIONS_DIR [--out verdicts.json] [--only INSTANCE]

Hardening against evaluator exploits:
- no tolerance slack: points must lie in the closed unit square (heilbronn); sphere points are projected, then scored
  (tammes); combinatorial objects are integers (type int, not bool or float) and are checked exactly
- heilbronn: triangle areas in exact rational arithmetic on the given floats
- keich: an independent area computation (all pairwise crossings, midpoint rule on the piecewise-linear union length);
  intercepts are bounded
- autocorrelation: direct (non-FFT) convolution after scale normalisation; step count capped
- a "beat" of a continuous record needs a relative margin of 1e-9, so rounding of a known optimum never counts
Stdlib + numpy only.
"""
from __future__ import annotations

import itertools
import json
import math
import os
import sys

# single-threaded BLAS: with every core busy, multi-threaded OpenBLAS thrashes (a 1 s check took > 600 s in CS4)
for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
RECORDS = json.loads((HERE / "records.json").read_text())
REL = 1e-9


def bad(why):
    return {"valid": False, "why": why}


def is_int(x):
    return type(x) is int


def floats(seq, n=None):
    if not isinstance(seq, list) or (n is not None and len(seq) != n):
        return None
    out = []
    for v in seq:
        if type(v) not in (int, float) or not math.isfinite(v):
            return None
        out.append(float(v))
    return out


# ---------------------------------------------------------------- continuous families
def heilbronn(sol, rec):
    pts = sol.get("points")
    if not isinstance(pts, list) or len(pts) != rec["n"]:
        return bad(f"need {rec['n']} points")
    P = []
    for p in pts:
        f = floats(p, 2)
        if f is None:
            return bad("each point must be [x, y] with finite numbers")
        if not (0.0 <= f[0] <= 1.0 and 0.0 <= f[1] <= 1.0):
            return bad("points must lie in the closed unit square [0,1]^2 (no tolerance)")
        P.append((Fraction(f[0]), Fraction(f[1])))
    best = None
    for a, b, c in itertools.combinations(P, 3):
        area = abs((b[0] - a[0]) * (c[1] - a[1]) - (c[0] - a[0]) * (b[1] - a[1])) / 2
        best = area if best is None or area < best else best
    if best == 0:
        return bad("three collinear points")
    return {"valid": True, "score": float(best)}


def tammes(sol, rec):
    pts = sol.get("points")
    if not isinstance(pts, list) or len(pts) != rec["n"]:
        return bad(f"need {rec['n']} points")
    P = []
    for p in pts:
        f = floats(p, 3)
        if f is None:
            return bad("each point must be [x, y, z] with finite numbers")
        P.append(f)
    P = np.asarray(P, dtype=np.float64)
    nrm = np.linalg.norm(P, axis=1)
    if np.max(np.abs(nrm - 1)) > 1e-6:
        return bad("points must be (close to) unit vectors; they are projected onto the sphere before scoring")
    P = P / nrm[:, None]
    G = np.clip(P @ P.T, -1.0, 1.0)
    iu = np.triu_indices(len(P), 1)
    t = int(np.argmax(G[iu]))
    cmax = float(G[iu][t])
    # the closest pair has the largest cosine; take the angle from its chord (more accurate than arccos near 1)
    chord = float(np.linalg.norm(P[iu[0][t]] - P[iu[1][t]]))
    if chord <= 0:
        return bad("coincident points")
    ang = math.degrees(2 * math.asin(min(1.0, chord / 2)))
    return {"valid": True, "score": ang, "max_cos": cmax}


def keich(sol, rec):
    b = floats(sol.get("intercepts"), 128)
    if b is None:
        return bad("need 128 finite intercepts")
    if max(abs(v) for v in b) > 4:
        return bad("intercepts must satisfy |b_i| <= 4")
    n = 128
    d = 1.0 / n
    a = np.arange(n) / n
    bb = np.asarray(b)
    # endpoint lines: top_i(x) = a_i x + b_i ; bot_i(x) = (a_i + d) x + (b_i - d)
    S = np.concatenate([a, a + d]); C = np.concatenate([bb, bb - d])
    ds = S[:, None] - S[None, :]; dc = C[None, :] - C[:, None]
    with np.errstate(divide="ignore", invalid="ignore"):
        X = dc / ds
    X = X[np.isfinite(X) & (X > 0) & (X < 1)]
    xs = np.unique(np.concatenate([[0.0, 1.0], X]))
    mids = (xs[:-1] + xs[1:]) / 2
    w = np.diff(xs)
    total = 0.0
    for k in range(0, len(mids), 4096):
        m = mids[k:k + 4096][:, None]
        top = a[None, :] * m + bb[None, :]
        bot = top - d * (1 - m)
        o = np.argsort(bot, axis=1)
        bot = np.take_along_axis(bot, o, 1); top = np.take_along_axis(top, o, 1)
        prev = np.maximum.accumulate(np.concatenate([np.full((len(m), 1), -np.inf), top[:, :-1]], 1), axis=1)
        L = np.sum(np.maximum(0.0, top - np.maximum(bot, prev)), axis=1)
        total += math.fsum((L * w[k:k + 4096]).tolist())
    return {"valid": True, "score": total}


def autocorr(sol, rec):
    h = sol.get("heights")
    if not isinstance(h, list) or not (10 <= len(h) <= rec["max_steps"]):
        return bad(f"heights must be a list of 10..{rec['max_steps']} numbers")
    h = np.asarray(h, dtype=np.float64)
    if not np.isfinite(h).all() or (h < 0).any():
        return bad("heights must be finite and non-negative")
    m = h.max()
    if m <= 0:
        return bad("all-zero function")
    h = h / m
    s = math.fsum(h.tolist())
    conv = np.convolve(h, h)  # direct convolution; (f*f) is piecewise linear, max at a knot
    return {"valid": True, "score": float(2 * len(h) * conv.max() / (s * s)), "n_steps": int(len(h))}


# ---------------------------------------------------------------- combinatorial families
def dts(sol, rec):
    rows = sol.get("rows")
    n, k = rec["n"], rec["k"]
    if not isinstance(rows, list) or len(rows) != n:
        return bad(f"need {n} rows")
    seen = set(); scope = 0
    for r in rows:
        if not isinstance(r, list) or len(r) != k + 1 or not all(is_int(x) for x in r):
            return bad(f"each row must be {k + 1} integers")
        if r[0] != 0 or any(r[j] <= r[j - 1] for j in range(1, k + 1)):
            return bad("rows must start at 0 and be strictly increasing")
        for i in range(k + 1):
            for j in range(i):
                dd = r[i] - r[j]
                if dd in seen:
                    return bad(f"repeated difference {dd}")
                seen.add(dd)
        scope = max(scope, r[-1])
    return {"valid": True, "score": scope}


def vdw(sol, rec):
    c = sol.get("coloring")
    if not isinstance(c, list) or not c or not all(is_int(x) and x in (0, 1) for x in c):
        return bad("coloring must be a non-empty list of integers 0/1")
    L = rec["ap"]; n = len(c); arr = np.asarray(c, dtype=np.int8)
    for dlt in range(1, (n - 1) // (L - 1) + 1):
        m = n - (L - 1) * dlt
        base = arr[:m]
        same = np.ones(m, dtype=bool)
        for t in range(1, L):
            same &= arr[t * dlt: t * dlt + m] == base
        if same.any():
            s0 = int(np.argmax(same))
            return bad(f"monochromatic {L}-AP: start {s0}, difference {dlt}")
    return {"valid": True, "score": n}


def blocks_of(sol, v, k):
    B = sol.get("blocks")
    if not isinstance(B, list) or not B:
        return None, "blocks must be a non-empty list"
    out = []
    for b in B:
        if not isinstance(b, list) or len(b) != k or not all(is_int(x) and 0 <= x < v for x in b) or len(set(b)) != k:
            return None, f"each block must be {k} distinct integers in 0..{v - 1}"
        out.append(tuple(sorted(b)))
    if len(set(out)) != len(out):
        return None, "duplicate blocks"
    return out, None


def packing_pairs(sol, rec):
    B, err = blocks_of(sol, rec["v"], rec["k"])
    if err:
        return bad(err)
    seen = set()
    for b in B:
        for p in itertools.combinations(b, 2):
            if p in seen:
                return bad(f"pair {p} in two blocks (minimum distance < 8)")
            seen.add(p)
    return {"valid": True, "score": len(B)}


def covering(sol, rec):
    B, err = blocks_of(sol, rec["v"], rec["k"])
    if err:
        return bad(err)
    masks = [sum(1 << x for x in b) for b in B]
    for t in itertools.combinations(range(rec["v"]), rec["t"]):
        tm = sum(1 << x for x in t)
        if not any(m & tm == tm for m in masks):
            return bad(f"{rec['t']}-subset {t} not covered")
    return {"valid": True, "score": len(B)}


def linear_code(sol, rec):
    G = sol.get("generator_matrix")
    n, k = rec["n"], rec["k"]
    if not isinstance(G, list) or len(G) != k or not all(isinstance(r, str) and len(r) == n and set(r) <= {"0", "1"} for r in G):
        return bad(f"generator_matrix must be {k} strings of {n} characters 0/1")
    rows = [int(r, 2) for r in G]
    # rank over GF(2)
    basis = []
    for r in rows:
        for bvec in basis:
            r = min(r, r ^ bvec)
        if r:
            basis.append(r)
    if len(basis) != k:
        return bad(f"rank {len(basis)} != {k}")
    dmin = n; cw = 0
    for i in range(1, 1 << k):  # Gray code walk over all nonzero codewords
        bit = (i & -i).bit_length() - 1
        cw ^= rows[bit]
        w = bin(cw).count("1")
        if w < dmin:
            dmin = w
    return {"valid": True, "score": dmin}


def difference_basis(sol, rec):
    B = sol.get("basis")
    n = rec["n"]
    if not isinstance(B, list) or not B or not all(is_int(x) and 0 <= x < n for x in B) or len(set(B)) != len(B):
        return bad(f"basis must be distinct integers in 0..{n - 1}")
    arr = np.asarray(sorted(B), dtype=np.int64)
    diffs = np.unique((arr[None, :] - arr[:, None])[np.triu_indices(len(arr), 1)])
    missing = n - 1 - int(np.count_nonzero((diffs >= 1) & (diffs <= n - 1)))
    if missing:
        return bad(f"{missing} differences in 1..{n - 1} are not represented")
    return {"valid": True, "score": len(B)}


CHECK = {"heilbronn": heilbronn, "tammes": tammes, "keich": keich, "autocorrelation_c1": autocorr, "dts": dts,
         "vdw": vdw, "packing_pairs": packing_pairs, "covering": covering, "linear_code": linear_code,
         "difference_basis": difference_basis}
CONTINUOUS = {"heilbronn", "tammes", "keich", "autocorrelation_c1"}


def main() -> None:
    sol_dir = Path(sys.argv[1])
    only = sys.argv[sys.argv.index("--only") + 1] if "--only" in sys.argv else None
    out = {}
    for inst, rec in RECORDS.items():
        if only and inst != only:
            continue
        f = sol_dir / f"{inst}.json"
        if not f.exists():
            out[inst] = bad("no solution file")
            continue
        try:
            sol = json.loads(f.read_text())
            v = CHECK[rec["family"]](sol, rec) if isinstance(sol, dict) else bad("solution must be a JSON object")
        except Exception as e:  # malformed input never crashes the referee
            v = bad(f"unreadable solution: {type(e).__name__}")
        if v.get("valid"):
            best, sc = rec["best_known"], v["score"]
            tol = REL * abs(best) if rec["family"] in CONTINUOUS else 0
            if rec["sense"] == "min":
                v["gap_rel"] = (sc - best) / abs(best)
                v["matches_record"] = sc <= best + tol
                v["beats_record"] = sc < best - tol
            else:
                v["gap_rel"] = (best - sc) / abs(best)
                v["matches_record"] = sc >= best - tol
                v["beats_record"] = sc > best + tol
        out[inst] = v
    text = json.dumps(out, indent=1)
    if "--out" in sys.argv:
        Path(sys.argv[sys.argv.index("--out") + 1]).write_text(text)
    print(text)


if __name__ == "__main__":
    main()
