#!/usr/bin/env python3
"""Token accounting per experiment condition (Claude's code). Sums assistant-message `usage` over the root session
file and every subagent session under session-artifacts/<root>/, grouped by provider/model.

    token_account.py [--json OUT]

Roots are found by the `cwd` of root session files under ~/.prime/agent/sessions.
"""
import collections, glob, json, os, re, sys

AGENT = os.path.expanduser("~/.prime/agent")
COND = re.compile(r"/Desktop/research/(07-swarm-engineering|08-swarm-math|09-swarm-hard|10-swarm-lean)/work/([A-Z][A-Z0-9]*)$")
# CS8 onwards: each condition has its own Prime Agent session directory (agent-sessions/<C>/sessions)
SESSION_DIRS = [f"{AGENT}/sessions"] + sorted(glob.glob(os.path.expanduser("~/Desktop/research/10-swarm-lean/agent-sessions/*/sessions")))
EXP = {"07-swarm-engineering": "CS3", "08-swarm-math": "CS4", "09-swarm-hard": "CS5", "10-swarm-lean": "CS6"}


def root_cwd(path):
    with open(path, errors="replace") as f:
        for _ in range(5):
            line = f.readline()
            m = re.search(r'"cwd":"([^"]+)"', line)
            if m:
                return m.group(1)
    return None


roots = collections.defaultdict(list)
base_of = {}  # root session id -> directory that holds sessions/ and session-artifacts/
for sd in SESSION_DIRS:
    for p in glob.glob(f"{sd}/*.jsonl"):
        c = root_cwd(p)
        m = COND.search(c or "")
        if m:
            cn = m.group(2)
            exp = ("CS7" if cn in ("TS", "TW") else "CS8" if cn.startswith("IA") else "CS9" if cn in ("TS2", "TW2")
                   else EXP[m.group(1)])  # CS7-CS9 share the 10-swarm-lean project
            rid = os.path.basename(p)[:-6]
            roots[(exp, cn)].append(rid); base_of[rid] = os.path.dirname(sd)

out = {}
for key in sorted(roots):
    agg = collections.defaultdict(lambda: collections.Counter())
    nsub = 0
    for r in roots[key]:
        B = base_of[r]
        files = [f"{B}/sessions/{r}.jsonl"]
        # subagents live under session-artifacts/<parent session id>/sub-*/<child session id>.jsonl; grandchildren
        # (rlm depth 2) live under session-artifacts/<child session id>/..., so follow child ids recursively
        subs, queue, seen = [], [r], set()
        while queue:
            sid = queue.pop()
            if sid in seen:
                continue
            seen.add(sid)
            # per-condition roots keep their workers under the global session-artifacts (CS9 finding): search both
            for f in sorted(set(glob.glob(f"{B}/session-artifacts/{sid}/**/*.jsonl", recursive=True)
                                + glob.glob(f"{AGENT}/session-artifacts/{sid}/**/*.jsonl", recursive=True))):
                if f.endswith("semantic-edges.jsonl"):
                    continue
                subs.append(f)
                queue.append(os.path.basename(f)[:-6])
        nsub += len(subs)
        for f in files + subs:
            for line in open(f, errors="replace"):
                if '"usage"' not in line or '"assistant"' not in line:
                    continue
                try:
                    d = json.loads(line)
                except Exception:
                    continue
                msg = d.get("message") or {}
                u = msg.get("usage") or {}
                if msg.get("role") != "assistant" or not u:
                    continue
                k = f'{msg.get("provider")}/{msg.get("model")}'
                c = agg[k]
                c["calls"] += 1
                for f2 in ("input", "output", "cacheRead", "cacheWrite"):
                    c[f2] += int(u.get(f2) or 0)
    out[f"{key[0]}-{key[1]}"] = {"roots": roots[key], "subagent_files": nsub, "by_model": {k: dict(v) for k, v in agg.items()}}

for name, d in out.items():
    tot = collections.Counter()
    for v in d["by_model"].values():
        tot.update(v)
    print(f"{name}: roots={len(d['roots'])} subagent_files={d['subagent_files']} calls={tot['calls']} "
          f"input={tot['input'] / 1e6:.1f}M cacheRead={tot['cacheRead'] / 1e6:.1f}M output={tot['output'] / 1e6:.2f}M")
    for k, v in sorted(d["by_model"].items()):
        print(f"    {k:40s} calls={v['calls']:6d} input={v['input'] / 1e6:7.1f}M cacheRead={v['cacheRead'] / 1e6:7.1f}M output={v['output'] / 1e6:6.2f}M")
if "--json" in sys.argv:
    json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)
