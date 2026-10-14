#!/usr/bin/env python3
"""CS4 referee (Claude's code; agents must never edit referee/). Verifies solutions/<instance>.json files.

    verify.py SOLUTIONS_DIR [--out verdicts.json]

Hardened against known evaluator exploits:
- circles: exact rational overlap and boundary checks (no float slack)
- autocorrelation: non-negativity, finiteness, scale normalisation (defeats the 1e-161 trick), size cap
- thomson: points must lie on the unit sphere to 1e-9 and are then projected; coincident points are rejected
- discrepancy: exact integer partial sums
Stdlib + numpy only.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
RECORDS = json.loads((HERE / "records.json").read_text())


def thomson(sol: dict, rec: dict) -> dict:
    p = np.asarray(sol["points"], dtype=np.float64)
    n = rec["n"]
    if p.shape != (n, 3) or not np.isfinite(p).all():
        return {"valid": False, "why": f"need {n}x3 finite points"}
    norms = np.linalg.norm(p, axis=1)
    if np.max(np.abs(norms - 1)) > 1e-9:
        return {"valid": False, "why": f"points off the unit sphere (max |r-1| = {np.max(np.abs(norms - 1)):.2e})"}
    p = p / norms[:, None]
    d = np.sqrt(((p[:, None, :] - p[None, :, :]) ** 2).sum(-1))
    iu = np.triu_indices(n, 1)
    dd = d[iu]
    if dd.min() < 1e-9:
        return {"valid": False, "why": "coincident points"}
    e = float(math.fsum((1.0 / dd).tolist()))
    return {"valid": True, "score": e}


def circles(sol: dict, rec: dict) -> dict:
    n = rec["n"]
    c, r = sol.get("centers"), sol.get("radii")
    if not (isinstance(c, list) and isinstance(r, list) and len(c) == n and len(r) == n):
        return {"valid": False, "why": f"need {n} centers and {n} radii"}
    try:
        C = [(Fraction(float(x)), Fraction(float(y))) for x, y in c]
        R = [Fraction(float(v)) for v in r]
    except (TypeError, ValueError, OverflowError):
        return {"valid": False, "why": "non-numeric or non-finite values"}
    for i, ((x, y), ri) in enumerate(zip(C, R)):
        if ri <= 0 or x - ri < 0 or x + ri > 1 or y - ri < 0 or y + ri > 1:
            return {"valid": False, "why": f"circle {i} not strictly inside the unit square or radius <= 0"}
    for i in range(n):
        xi, yi = C[i]
        for j in range(i + 1, n):
            xj, yj = C[j]
            if (xi - xj) ** 2 + (yi - yj) ** 2 < (R[i] + R[j]) ** 2:
                return {"valid": False, "why": f"circles {i} and {j} overlap (exact check)"}
    return {"valid": True, "score": float(sum(R))}


def autocorr_c1(sol: dict, rec: dict) -> dict:
    h = np.asarray(sol.get("heights", []), dtype=np.float64)
    n = h.size
    if n < 1 or n > 100_000 or not np.isfinite(h).all():
        return {"valid": False, "why": "heights must be 1..100000 finite numbers"}
    if (h < 0).any():
        return {"valid": False, "why": "negative height: f must be non-negative"}
    m = h.max()
    if m <= 0:
        return {"valid": False, "why": "all-zero function"}
    h = h / m                       # scale invariance: the ratio is unchanged, the tiny-number exploit is not
    s = math.fsum(h.tolist())
    conv = np.convolve(h, h)        # (f*f) at the knots t_k = -1/2 + k/(2n) equals conv[k] / (2n)
    # f*f is piecewise linear between knots, so its maximum is at a knot; C = 2n * max(conv) / s^2
    return {"valid": True, "score": float(2 * n * conv.max() / (s * s)), "n_steps": int(n)}


def discrepancy(sol: dict, rec: dict) -> dict:
    a = sol.get("signs")
    if not isinstance(a, list) or not a or any(v not in (1, -1) for v in a):
        return {"valid": False, "why": "signs must be a non-empty list of +1/-1"}
    N, C = len(a), rec["C"]
    for d in range(1, N + 1):
        s = 0
        for k in range(d, N + 1, d):
            s += a[k - 1]
            if abs(s) > C:
                return {"valid": False, "why": f"discrepancy exceeds {C} at d={d}, k={k // d}"}
    return {"valid": True, "score": N}


CHECK = {"thomson": thomson, "circles_sum_radii": circles, "autocorrelation_c1": autocorr_c1, "erdos_discrepancy": discrepancy}
TOL = {"thomson": 1e-6, "circles_sum_radii": 0.0, "autocorrelation_c1": 0.0, "erdos_discrepancy": 0}


def main() -> None:
    sol_dir = Path(sys.argv[1])
    out = {}
    for inst, rec in RECORDS.items():
        f = sol_dir / f"{inst}.json"
        if not f.exists():
            out[inst] = {"valid": False, "why": "no solution file"}
            continue
        try:
            v = CHECK[rec["family"]](json.loads(f.read_text()), rec)
        except Exception as e:  # malformed input never crashes the referee
            v = {"valid": False, "why": f"unreadable solution: {type(e).__name__}"}
        if v.get("valid"):
            best, tol, sc = rec["best_known"], TOL[rec["family"]], v["score"]
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
