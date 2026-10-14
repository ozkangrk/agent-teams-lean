#!/usr/bin/env python3
"""List formal-conjectures declarations by category whose proof is exactly `sorry` (Claude's code).

    extract.py {open|solved|test} [--since YYYY-MM-DD] [--max-len N] > problems.jsonl

Each output line has: id, module, theorem (fully qualified), file, added (git date), statement (source text), and a
`answer_sorry` flag. Declarations whose statement contains `answer(sorry)` cannot be checked against a fixed type,
so they are flagged and should be excluded.
"""
import json, re, subprocess, sys
from pathlib import Path

UP = Path.home() / "Desktop/research/10-swarm-lean/upstream/formal-conjectures"
cat = sys.argv[1]
since = sys.argv[sys.argv.index("--since") + 1] if "--since" in sys.argv else ""
maxlen = int(sys.argv[sys.argv.index("--max-len") + 1]) if "--max-len" in sys.argv else 10**9

log = subprocess.run(["git", "log", "--diff-filter=A", "--name-only", "--format=@@%cd", "--date=short", "--",
                      "FormalConjectures"], cwd=UP, capture_output=True, text=True).stdout
added, d = {}, None
for line in log.splitlines():
    if line.startswith("@@"):
        d = line[2:]
    elif line.endswith(".lean"):
        added.setdefault(line, d)

DECL = re.compile(r"@\[category research " + cat + r"[^\]]*\]\s*\n\s*(?:theorem|lemma)\s+([^\s(:{\[]+)(.*?):=\s*by\s*\n\s*sorry\b", re.S) \
    if cat in ("open", "solved") else \
    re.compile(r"@\[category test[^\]]*\]\s*\n\s*(?:theorem|lemma)\s+([^\s(:{\[]+)(.*?):=\s*by\s*\n\s*sorry\b", re.S)

for f in sorted(UP.glob("FormalConjectures/**/*.lean")):
    rel = str(f.relative_to(UP))
    if since and (added.get(rel) or "") < since:
        continue
    src = f.read_text(errors="replace")
    for m in DECL.finditer(src):
        name, stmt = m.group(1), m.group(2).strip()
        if len(stmt) > maxlen:
            continue
        # namespace stack at the declaration position
        ns = []
        for tok in re.finditer(r"^\s*(namespace|end)\s+([\w.«»']+)", src[:m.start()], re.M):
            if tok.group(1) == "namespace":
                ns.append(tok.group(2))
            elif ns and ns[-1] == tok.group(2):
                ns.pop()
        full = ".".join(ns + [name]) if not name.startswith("_root_.") else name[len("_root_."):]
        parts = rel[:-5].split("/")
        module = ".".join(p if re.fullmatch(r"[A-Za-z_][\w']*", p) else f"«{p}»" for p in parts)
        print(json.dumps({"id": f"{parts[-2]}-{parts[-1]}-{name}", "module": module, "theorem": full, "file": rel,
                          "added": added.get(rel), "answer_sorry": "answer(sorry)" in stmt, "statement": stmt},
                         ensure_ascii=False))
