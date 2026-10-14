#!/usr/bin/env python3
"""Referee snapshot of a Lean condition workspace (Claude's code).

    lean_snapshot.py WORKDIR [--append LOG.jsonl] [--final OUT.json]

Runs the referee on every proofs/*.lean declaring swarm_proof/swarm_disproof. Each file is mapped to its problem by
exact id, or else by the OEIS/Erdős number in the file name. Prints {"t", "cond", "accepted": {id: [files]}}.
--append adds the line to a time-series log (for the proofs-vs-time curve); --final writes a per-id verdict for
every problem.
"""
import hashlib, json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

W = Path(sys.argv[1]).resolve(); P = W.parent.parent
probs = [json.loads(l) for l in (W / "PROBLEMS.jsonl").read_text().splitlines() if l.strip()]
byid = {p["id"]: p for p in probs}


CACHE = P / "conditions/.snapshot_cache.json"   # sha256(file)+id -> verdict (the referee is deterministic)
cache = json.loads(CACHE.read_text()) if CACHE.exists() else {}


def referee(p, f):
    key = hashlib.sha256(Path(f).read_bytes()).hexdigest() + ":" + p["id"]
    if key in cache:
        return cache[key]
    # pinned to the spare cores 18-19 so verification never competes with the conditions' cores
    r = subprocess.run(["taskset", "-c", "18,19", "python3", "-I", str(P / "referee/check.py"), "--module", p["module"], "--theorem", p["theorem"],
                        "--proof", str(f)], capture_output=True, text=True, timeout=1500)
    try:
        v = json.loads(r.stdout.strip().splitlines()[-1])
    except Exception:
        return {"accepted": False, "why": r.stderr[-300:]}
    cache[key] = v
    return v


acc, verdicts, jobs = {}, {}, []
# any .lean file under proofs/ counts, including nested layouts such as proofs/<id>/Submission.lean (CS9 TW2; D10).
# A file maps to a problem by an exact id in its relative path, else by the OEIS/Erdős number in the path.
for f in sorted((W / "proofs").rglob("*.lean")):
    src = f.read_text(errors="replace")
    if not re.search(r"^\s*theorem\s+swarm_(proof|disproof)\b", src, re.M):
        continue
    rel = f.relative_to(W / "proofs")
    parts = [x[:-5] if x.endswith(".lean") else x for x in rel.parts]
    cands = [byid[x] for x in parts if x in byid][:1]
    stem = str(rel.with_suffix(""))
    if not cands:
        m = re.search(r"(\d{2,7})", stem)
        if m:
            cands = [p for p in probs if p["file"].split("/")[-1][:-5].lstrip("0") == m.group(1).lstrip("0")]
    jobs += [(p, f) for p in cands]
with ThreadPoolExecutor(2) as ex:
    results = list(ex.map(lambda pf: (pf[0], pf[1], referee(*pf)), jobs))
for p, f, v in results:
    if v.get("accepted"):
        name = str(f.relative_to(W / "proofs"))
        acc.setdefault(p["id"], []).append(name)
        verdicts[p["id"]] = {**v, "file": name}
CACHE.write_text(json.dumps(cache))
out = {"t": time.strftime("%Y-%m-%dT%H:%M:%S"), "cond": W.name, "n_accepted": len(acc), "accepted": acc}
print(json.dumps(out, ensure_ascii=False))
if "--append" in sys.argv:
    with open(sys.argv[sys.argv.index("--append") + 1], "a") as fh:
        fh.write(json.dumps(out, ensure_ascii=False) + "\n")
if "--final" in sys.argv:
    full = {p["id"]: verdicts.get(p["id"], {"accepted": False}) for p in probs}
    Path(sys.argv[sys.argv.index("--final") + 1]).write_text(json.dumps(full, indent=1, ensure_ascii=False))
