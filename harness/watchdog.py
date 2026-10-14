#!/usr/bin/env python3
"""Tool-call watchdog (Claude's code). One instance per condition; identical rule for every condition.

    watchdog.py --workdir W --socket SOCK --until EPOCH [--limit-min 20]

Rule: if a session has been inside one tool call for more than --limit-min minutes (isRunningTools and no activity
since), the foreground commands that call started are terminated: direct children of that session's REPL kernel
that are older than the limit. Background shells started through the harness (the `_prime_agent_gate` wrapper) are
never touched, so long optimisation jobs run as background work are unaffected. The agent then sees its tool call
return with an error and continues. Every action is appended to W/watchdog.log (evidence for the paper).
If the session is blocked but no such command exists (a pure-Python loop or an `await` inside the kernel), the
turn is aborted through the daemon (what Esc does) and a standard continue notice is sent, at most once per 5 min
(CS6 D2). The kernel ignores a raw SIGINT, as verified 2026-10-12.
Added mid-run in CS4 (2026-10-11 ~17:55) after S1 blocked for 34 min on an exponential brute-force test; see
conditions/DEVIATIONS.md.
"""
import argparse, json, os, signal, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("--workdir", required=True); ap.add_argument("--socket", required=True)
ap.add_argument("--until", type=float, required=True); ap.add_argument("--limit-min", type=float, default=20)
ap.add_argument("--dry-run", action="store_true", help="one pass, print instead of acting")
a = ap.parse_args()
W = Path(a.workdir).resolve(); LOG = W / "watchdog.log"; LIMIT = a.limit_min * 60
TICKS = os.sysconf("SC_CLK_TCK"); BOOT = time.time() - float(Path("/proc/uptime").read_text().split()[0])


def log(msg):
    if a.dry_run:
        print(msg); return
    with LOG.open("a") as f:
        f.write(f"{time.strftime('%Y-%m-%dT%H:%M:%S')} {msg}\n")


def children(pid):
    # scan ppids: /proc/PID/task/TID/children is per-thread and misses children forked by other threads
    out = []
    for d in Path("/proc").iterdir():
        if d.name.isdigit():
            try:
                if int((d / "stat").read_text().rsplit(")", 1)[1].split()[1]) == pid:
                    out.append(int(d.name))
            except (OSError, IndexError, ValueError):
                pass
    return out


def cmdline(pid):
    try:
        return Path(f"/proc/{pid}/cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace").strip()
    except OSError:
        return ""


def started(pid):
    try:
        return BOOT + int(Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[19]) / TICKS
    except (OSError, IndexError, ValueError):
        return time.time()


def zombie(pid):
    try:
        return Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0] == "Z"
    except (OSError, IndexError):
        return True


def tree(pid):
    out = [pid]
    for c in children(pid):
        out += tree(c)
    return out


def sessions():
    try:
        r = subprocess.run(["prime-agent", "--daemon-socket", a.socket, "list", "--json"], capture_output=True, text=True, timeout=60)
        return json.loads(r.stdout).get("sessions", [])
    except Exception as e:
        log(f"list failed: {e}")
        return []


last_sigint = {}
log(f"watchdog start limit={a.limit_min:g}min until={time.strftime('%H:%M', time.localtime(a.until))}")
while time.time() < a.until:
    now = time.time()
    for s in sessions():
        if not s.get("isRunningTools") or not s.get("workerPid") or not s.get("lastActivityAt"):
            continue
        last = datetime.fromisoformat(s["lastActivityAt"].replace("Z", "+00:00")).astimezone(timezone.utc).timestamp()
        if now - last < LIMIT:
            continue
        # the kernel is the python process running rlm.repl; with the bwrap sandbox wrapper (kernel_sandbox.sh) the
        # worker's direct child is `bwrap ... python -m rlm.repl`, so descend through bwrap to the real kernel
        # kernel_sandbox_v2 adds a PID namespace, so there are two bwrap layers (bwrap -> namespace init -> kernel):
        # descend through every bwrap whose command line runs rlm.repl until the real kernel process
        def kernels_of(pid):
            out = []
            for k in children(pid):
                cl = cmdline(k)
                if "rlm.repl" not in cl:
                    continue
                out += kernels_of(k) if os.path.basename(cl.split(" ", 1)[0]) == "bwrap" else [k]
            return out
        kernels = kernels_of(s["workerPid"])
        for k in kernels:
            acted = False
            for c in children(k):
                cl = cmdline(c)
                if "_prime_agent_gate" in cl or now - started(c) < LIMIT or zombie(c):
                    continue
                acted = True
                victims = tree(c)
                if a.dry_run:
                    log(f"DRY would terminate pid {c} of session {s['id']} age {(now - started(c)) / 60:.0f} min: {cl[:120]!r}"); continue
                log(f"session {s['id']} (depth {s.get('rlmDepth')}) blocked {(now - last) / 60:.0f} min; terminating pid {c} "
                    f"(age {(now - started(c)) / 60:.0f} min, tree {victims}): {cl[:300]!r}")
                for v in reversed(victims):
                    try:
                        os.kill(v, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                time.sleep(10)
                for v in victims:
                    try:
                        os.kill(v, signal.SIGKILL); log(f"  pid {v} needed SIGKILL")
                    except ProcessLookupError:
                        pass
            # nothing to terminate: the call is blocked inside the kernel itself (a pure-Python loop or an `await`).
            # Raw SIGINT is ignored by the Prime Agent kernel, so use the daemon's own `abort` (what Esc does in the
            # TUI), then send the standard watchdog notice so the session continues. At most once per 5 min.
            if not acted and now - last_sigint.get(k, 0) >= 300:
                if a.dry_run:
                    log(f"DRY would abort session {s['id']} (blocked {(now - last) / 60:.0f} min, in-kernel)"); continue
                r = subprocess.run(["python3", "-I", str(Path(__file__).with_name("pa_abort.py")), a.socket,
                                    s.get("activeSessionId") or s["id"]], capture_output=True, text=True, timeout=90)
                log(f"session {s['id']} (depth {s.get('rlmDepth')}) blocked {(now - last) / 60:.0f} min in-kernel; "
                    f"abort -> {(r.stdout or r.stderr).strip()[:120]}")
                time.sleep(5)
                msg = ("WATCHDOG: Arac cagrin 20 dakikayi astigi icin kesildi (TASK.md kurali). Calismana devam et; "
                       "20 dakikadan uzun isleri arka plan kabugunda calistir ve sonucu sonra kontrol et.")
                r2 = subprocess.run(["prime-agent", "--daemon-socket", a.socket, "send", s["id"], msg],
                                    capture_output=True, text=True, timeout=60)
                log(f"  continue notice -> {r2.stdout.strip()[:80]}")
                last_sigint[k] = now
    if a.dry_run:
        break
    time.sleep(60)
log("watchdog stop (until reached)")
