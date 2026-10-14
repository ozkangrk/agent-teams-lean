#!/usr/bin/env python3
"""Abort the current turn of a Prime Agent session through the daemon socket, the same `abort` command the TUI
sends on Esc (Claude's helper). It interrupts a tool call that is blocked inside the kernel.

    pa_abort.py SOCKET ACTIVE_SESSION_ID [--resume-only]

After `abort` the daemon suspends the session's queued input; `resume_queue` re-opens it, so a follow-up message can
be admitted. With --resume-only, only resume_queue is sent.
"""
import json, socket, sys, uuid
sock, sid = sys.argv[1], sys.argv[2]
s = socket.socket(socket.AF_UNIX); s.settimeout(30); s.connect(sock)
f = s.makefile("rwb")
hello = None
while hello is None:
    line = f.readline()
    if not line:
        sys.exit("no hello")
    d = json.loads(line)
    if d.get("type") == "daemon_hello":
        hello = d
cid = "watchdog:" + uuid.uuid4().hex


def cmd(kind):
    rid = kind + "_" + uuid.uuid4().hex[:8]
    env = {"type": "command", "id": rid, "protocol": hello["protocol"], "clientId": cid,
           "command": {"type": kind, "id": rid, "activeSessionId": sid}}
    f.write((json.dumps(env) + "\n").encode()); f.flush()
    while True:
        line = f.readline()
        if not line:
            sys.exit("closed")
        d = json.loads(line)
        if d.get("type") == "response" and d.get("id") == rid:
            return d


out = []
if "--resume-only" not in sys.argv:
    out.append(cmd("abort"))
out.append(cmd("resume_queue"))
print(json.dumps([{k: d.get(k) for k in ("command", "success", "error")} for d in out])[:300])
