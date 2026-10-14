#!/usr/bin/env python3
"""Build the leak-free views shown to CS7 agents (Claude's code).

    sanitize.py

1. sanitized/FormalConjectures/: a copy of the upstream statement sources with every comment and docstring removed
   (`--`, `/- -/`, `/-- -/`, `/-! -/`, nested) and every `formal_proof ...` attribute clause dropped. Compiled
   .olean files are untouched, so imports and the referee behave exactly as before.
2. sanitized/library/oeis/: OEIS entries without any line dated 2026 or mentioning a resolution (proved, disproved,
   counterexample, Adamczewski, OEIS Open, arXiv 26xx).
The sandbox mounts these over the original paths for CS7 agents only.
"""
import json, re, shutil
from pathlib import Path

P = Path.home() / "Desktop/research/10-swarm-lean"
UP = P / "upstream/formal-conjectures/FormalConjectures"
OUT = P / "sanitized"


def strip_lean(src: str) -> str:
    out, i, n, depth = [], 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        if depth == 0 and not in_str and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if not in_str and src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth > 0:
            if src.startswith("-/", i):
                depth -= 1; i += 2
            else:
                i += 1
            continue
        if c == '"' and (i == 0 or src[i - 1] != "\\"):
            in_str = not in_str
        out.append(c); i += 1
    s = "".join(out)
    s = re.sub(r",?\s*(?:conditional\s+)?formal_proof\s+using\s+\w+\s+at\s*\"[^\"]*\"", "", s)
    s = re.sub(r"\n\s*\n\s*\n+", "\n\n", s)
    return s


def main():
    if OUT.exists():
        shutil.rmtree(OUT)
    n = 0
    for f in UP.rglob("*.lean"):
        dst = OUT / "FormalConjectures" / f.relative_to(UP)
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(strip_lean(f.read_text(errors="replace")))
        n += 1
    LEAK = re.compile(r"2026|Adamczewski|OEIS Open|[Pp]rove[dn]|[Dd]isprove|[Cc]ounterexample|[Rr]efute|arXiv:26\d\d|abs/26\d\d")
    (OUT / "library/oeis").mkdir(parents=True, exist_ok=True)
    m = dropped = 0
    for f in (P / "library/oeis").glob("*.json"):
        d = json.loads(f.read_text())
        entries = d if isinstance(d, list) else d.get("results") or []
        for e in entries:
            for k, v in list(e.items()):
                if isinstance(v, list):
                    keep = [x for x in v if not (isinstance(x, str) and LEAK.search(x))]
                    dropped += len(v) - len(keep); e[k] = keep
        (OUT / "library/oeis" / f.name).write_text(json.dumps(d, ensure_ascii=False))
        m += 1
    print(f"sanitized {n} Lean files, {m} OEIS entries ({dropped} leaking lines dropped)")


if __name__ == "__main__":
    main()
