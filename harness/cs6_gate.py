#!/usr/bin/env python3
"""Completion gate for CS6 (Claude's). Usage: python3 -I cs6_gate.py <work/Cx dir>
Passes when the time budget is nearly used, the ledger is non-empty, and the referee accepts every id that
RESULT.md claims."""
import json, re, subprocess, sys, time
from pathlib import Path
W = Path(sys.argv[1]).resolve(); P = W.parent.parent; fails = []
left = float((W / ".launched").read_text()) + float((W / ".budget_hours").read_text()) * 3600 - 15 * 60 - time.time()
if left > 0:
    fails.append(f"time budget not used up: keep working for another {left / 60:.0f} minutes, then finish")
if not (W / "ledger.jsonl").exists() or not (W / "ledger.jsonl").read_text().strip():
    fails.append("ledger.jsonl is empty")
probs = {json.loads(l)["id"]: json.loads(l) for l in (W / "PROBLEMS.jsonl").read_text().splitlines() if l.strip()}
res = W / "RESULT.md"
m = re.search(r"```json\s*(\{.*?\})\s*```", res.read_text(), re.S) if res.exists() else None
claims = (json.loads(m.group(1)).get("accepted") if m else None)
if not isinstance(claims, list):
    fails.append('RESULT.md needs a ```json {"accepted": [ids]}``` block')
    claims = []
ok = []
for i in claims:
    if i not in probs:
        fails.append(f"unknown id {i}"); continue
    pr = W / "proofs" / f"{i}.lean"
    r = subprocess.run(["python3", "-I", str(P / "referee/check.py"), "--module", probs[i]["module"], "--theorem",
                        probs[i]["theorem"], "--proof", str(pr)], capture_output=True, text=True, timeout=1500)
    v = json.loads(r.stdout.strip().splitlines()[-1]) if r.stdout.strip() else {"accepted": False, "why": r.stderr[-300:]}
    (ok if v.get("accepted") else fails).append(i if v.get("accepted") else f"{i}: referee rejects ({v.get('stage')}: {str(v.get('why'))[:200]})")
print(json.dumps({"accepted_verified": ok}, indent=1))
print("\n".join(f"[FAIL] {f}" for f in fails) or "[PASS] cs6 gate")
sys.exit(1 if fails else 0)
