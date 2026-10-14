#!/usr/bin/env python3
"""Condition supervisor (Claude's code). One instance per condition, started in the background.

    supervisor.py --workdir W --tmux NAME --deadline EPOCH [--socket SOCK] [--nudge-gate "CMD"] [--grace-min 15]

Every 2 minutes it:
- if --nudge-gate is set and the orchestrator (rlmDepth 0, cwd == W) is idle (no tools, no subagents, not streaming)
  for >= 3 min before (deadline - 20 min): runs the gate command and sends its output with a "keep improving" message
  (at most every 10 min);
- if --precheck-min is set: once, at (deadline - precheck), sends the gate output even if the orchestrator is busy;
- at the deadline: sends a "time is up, finalise RESULT.md now" message once, then after --grace-min closes the tmux
  session.
Every action is appended to W/supervisor.log (evidence for the paper). The same code supervises every condition.
"""
import argparse, json, subprocess, time
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("--workdir", required=True); ap.add_argument("--tmux", required=True)
ap.add_argument("--deadline", type=float, required=True); ap.add_argument("--socket")
ap.add_argument("--nudge-gate"); ap.add_argument("--tmux-socket", help="tmux -L socket name (default server if omitted)"); ap.add_argument("--grace-min", type=float, default=15)
ap.add_argument("--precheck-min", type=float, default=0, help="once, this many minutes before the deadline, send the gate output to the orchestrator even if it is busy (0 = off)")
ap.add_argument("--stop-unit", help="systemd user unit of the agent daemon to stop after the tmux session is closed (CS7: the daemon outlived the session)")
a = ap.parse_args()
W = Path(a.workdir).resolve(); LOG = W / "supervisor.log"
PA = ["prime-agent"] + (["--daemon-socket", a.socket] if a.socket else [])


def log(msg):
    with LOG.open("a") as f:
        f.write(f"{time.strftime('%Y-%m-%dT%H:%M:%S')} {msg}\n")


def orchestrator():
    try:
        out = subprocess.run(PA + ["list", "--json"], capture_output=True, text=True, timeout=60).stdout
        for s in json.loads(out).get("sessions", []):
            if s.get("rlmDepth") == 0 and Path(s.get("cwd", "")).resolve() == W:
                return s
    except Exception as e:
        log(f"list failed: {e}")
    return None


def send(sid, text):
    r = subprocess.run(PA + ["send", sid, text], capture_output=True, text=True, timeout=60)
    log(f"sent to {sid}: {text[:160]!r} -> {r.stdout.strip()[:80]}")


idle_since, last_nudge, final_sent, prechecked = None, 0.0, None, False
log(f"supervisor start deadline={time.strftime('%H:%M', time.localtime(a.deadline))} nudge={'yes' if a.nudge_gate else 'no'}")
while True:
    now = time.time()
    s = orchestrator()
    if final_sent is None and now >= a.deadline:
        if s:
            send(s["id"], "SURE DOLDU: 10 dakika icinde RESULT.md dosyasini referee'nin dogruladigi en iyi sonuclarla guncelle, ledger'i tamamla ve dur. Yeni deneme baslatma.")
        final_sent = now
    if final_sent is not None and now >= final_sent + a.grace_min * 60:
        subprocess.run(["tmux"] + (["-L", a.tmux_socket] if a.tmux_socket else []) + ["kill-session", "-t", a.tmux], capture_output=True)
        log(f"deadline + grace reached: tmux session {a.tmux} closed")
        if a.stop_unit:
            r = subprocess.run(["systemctl", "--user", "stop", a.stop_unit], capture_output=True, text=True)
            log(f"agent unit {a.stop_unit} stopped (rc={r.returncode})")
        break
    if s and a.nudge_gate and a.precheck_min and not prechecked and final_sent is None and now >= a.deadline - a.precheck_min * 60:
        g = subprocess.run(a.nudge_gate, shell=True, capture_output=True, text=True, timeout=1800)
        send(s["id"], f"ON KONTROL (her kosula ayni, sure bitmeden {a.precheck_min:.0f} dk once): gate ciktisi asagida. Bitirirken RESULT.md bu kontrolden gecmeli.\n{(g.stdout + g.stderr)[-1500:]}")
        prechecked = True
    if s and a.nudge_gate and final_sent is None:
        busy = s.get("activity") != "idle" or s.get("isRunningTools") or s.get("hasRunningSubagents") or s.get("isStreaming") or s.get("isBashRunning")
        idle_since = None if busy else (idle_since or now)
        if idle_since and now - idle_since >= 180 and now < a.deadline - 1200 and now - last_nudge >= 600:
            g = subprocess.run(a.nudge_gate, shell=True, capture_output=True, text=True, timeout=1800)
            left = (a.deadline - now) / 60
            send(s["id"], f"Butce dolmadi (kalan ~{left:.0f} dk). Gate ciktisi:\n{(g.stdout + g.stderr)[-1500:]}\nIyilestirmeye devam et; her denemeyi ledger'a yaz.")
            last_nudge, idle_since = now, None
    time.sleep(120)
