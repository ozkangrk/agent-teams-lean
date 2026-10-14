#!/usr/bin/env python3
"""CS3 referee (written by Claude; agents must never edit anything under referee/).

    referee.py baseline                 # build+record the pinned baseline (once, by Claude)
    referee.py judge WORKTREE [--tag T] # build WORKTREE, check correctness, benchmark; writes verdict JSON

Exit code of `judge`: 0 = correct (speed recorded), 1 = incorrect or build/test failure, 2 = environment problem.
Stdlib only. All GPU work runs under an exclusive flock so concurrent agents queue instead of interfering.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import shutil
import signal
import statistics
import subprocess
import sys
import time
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJ = HERE.parent
ZIG = Path.home() / ".local/opt/zig-0.17.0/zig"
NVCC = "/usr/local/cuda/bin/nvcc"
PINNED = "56150e6d052ef65b9fc258425b055affa28d7456"
MODEL = PROJ / "models/ref"               # referee-owned writable copy of the pristine checkpoint
BASELINE = HERE / "baseline/baseline.json"
LOCK = "/tmp/swarm-gpu.lock"
PORT = 8099
NEAR_TIE = 0.10                          # nats: a divergence here is a near-tie flip, not an error
MEAN_DLP, MAX_DLP = 0.02, 0.25           # logprob agreement before the first divergence
DECODE_RUNS, PREFILL_RUNS = 5, 3


def sh(cmd, cwd=None, timeout=7200, log=None):
    r = subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True, timeout=timeout)
    if log:
        Path(log).write_text(r.stdout + r.stderr)
    return r.returncode, (r.stdout + r.stderr)[-3000:]


def build(worktree: Path, prefix: Path, log: Path) -> Path | None:
    code, out = sh(f"{ZIG} build -Dnvcc={NVCC} -Doptimize=fast --prefix {prefix} -j16 fatbins install native",
                   cwd=worktree, log=log)
    b = prefix / "native/bin/tensorfold-native"
    return b if code == 0 and b.exists() else None


def unit_tests(worktree: Path, log: Path) -> bool:
    code, _ = sh(f"{ZIG} build test test-cuda-host test-server-cpu -Doptimize=fast -j16", cwd=worktree, log=log)
    return code == 0


def gpu_exclusive() -> str | None:
    """Reasons the GPU is not exclusive, or None."""
    procs = subprocess.run("ps -eo args", shell=True, capture_output=True, text=True).stdout
    for pat in ("tensorfold-native serve", "vllm serve", "vllm.entrypoints"):
        if pat in procs:
            return f"another GPU server is running ({pat})"
    util = subprocess.run("nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits",
                          shell=True, capture_output=True, text=True).stdout.strip() or "0"
    if int(util.split()[0]) > 15:
        return f"GPU busy ({util}% utilisation)"
    return None


class Server:
    def __init__(self, binary: Path, log: Path, drafts: bool):
        cmd = [str(binary), "serve", str(MODEL), "--port", str(PORT), "--host", "127.0.0.1", "--name", "ref",
               "--parallel", "1", "--context", "16384", "--temperature", "0", "--no-thinking", "--no-update-check"]
        if not drafts:
            cmd.append("--no-drafts")
        self.p = subprocess.Popen(cmd, stdout=open(log, "w"), stderr=subprocess.STDOUT, start_new_session=True)
        t0 = time.time()
        while time.time() - t0 < 900:
            if self.p.poll() is not None:
                raise RuntimeError(f"server exited (code {self.p.returncode}); see {log}")
            try:
                urllib.request.urlopen(f"http://127.0.0.1:{PORT}/v1/models", timeout=3)
                return
            except Exception:
                time.sleep(2)
        self.stop()
        raise RuntimeError("server not ready in 900 s")

    def chat(self, messages, max_tokens, logprobs=False, timeout=900):
        body = {"messages": messages, "max_tokens": max_tokens, "temperature": 0}
        if logprobs:
            body.update(logprobs=True, top_logprobs=2)
        req = urllib.request.Request(f"http://127.0.0.1:{PORT}/v1/chat/completions", data=json.dumps(body).encode(),
                                     headers={"Content-Type": "application/json"})
        t0 = time.time()
        with urllib.request.urlopen(req, timeout=timeout) as r:
            d = json.loads(r.read())
        return d, time.time() - t0

    def stop(self):
        if self.p.poll() is None:
            os.killpg(self.p.pid, signal.SIGTERM)
            try:
                self.p.wait(120)
            except subprocess.TimeoutExpired:
                os.killpg(self.p.pid, signal.SIGKILL)
        time.sleep(8)


def suite() -> list[dict]:
    s = json.loads((HERE / "suite.json").read_text())
    log = "\n".join(f"2026-10-11 08:{i // 60 % 60:02d}:{i % 60:02d} worker-{i % 7} batch {i} took {(i * 37) % 900} ms status={'ok' if i % 53 else 'RETRY'}"
                    for i in range(330))
    s.append({"id": "long-8k", "messages": [{"role": "user", "content": "Here is a log:\n" + log +
                                             "\nWhich batches have status RETRY? List their numbers."}]})
    return s


def record_outputs(srv: Server) -> dict:
    out = {}
    for item in suite():
        d, _ = srv.chat(item["messages"], 256, logprobs=True)
        rows = (d["choices"][0].get("logprobs") or {}).get("content") or []
        out[item["id"]] = [{"t": r["token"], "lp": r["logprob"],
                            "alt": [(a["token"], a["logprob"]) for a in r.get("top_logprobs", [])]} for r in rows]
    return out


def bench(srv: Server, prefill: bool) -> dict:
    srv.chat([{"role": "user", "content": "Say hi."}], 8)
    dec = []
    for _ in range(DECODE_RUNS):
        d, dt = srv.chat([{"role": "user", "content": "Write a detailed 600-word essay about lighthouses."}], 512)
        dec.append(d["usage"]["completion_tokens"] / dt)
    res = {"decode_tok_s": round(statistics.median(dec), 2), "decode_runs": [round(x, 2) for x in dec]}
    if prefill:
        long = suite()[-1]["messages"][0]["content"]
        pre = []
        for i in range(PREFILL_RUNS):
            # a unique first line defeats the prompt-state cache, so this measures real prefill
            nonce = f"Run {i} at {time.time_ns()}: read the whole log before answering.\n"
            d, dt = srv.chat([{"role": "user", "content": nonce + long + "\n(Answer: ok)"}], 1)
            pre.append(d["usage"]["prompt_tokens"] / dt)
        res.update(prefill_tok_s=round(statistics.median(pre), 1), prefill_runs=[round(x, 1) for x in pre])
    return res


def compare(base: dict, cand: dict) -> dict:
    report = {"prompts": len(base), "identical": 0, "near_tie_flips": 0, "errors": []}
    for pid, b in base.items():
        c = cand.get(pid, [])
        n = min(len(b), len(c))
        div = next((i for i in range(n) if b[i]["t"] != c[i]["t"]), None)
        upto = div if div is not None else n
        dl = [abs(b[i]["lp"] - c[i]["lp"]) for i in range(upto)]
        if dl and (sum(dl) / len(dl) > MEAN_DLP or max(dl) > MAX_DLP):
            report["errors"].append(f"{pid}: logprob drift mean {sum(dl) / len(dl):.4f} max {max(dl):.4f} before divergence")
            continue
        if div is None:
            if len(b) != len(c):
                report["errors"].append(f"{pid}: length {len(c)} != baseline {len(b)} with no token divergence")
            else:
                report["identical"] += 1
            continue
        alts = b[div]["alt"]
        gap = (alts[0][1] - alts[1][1]) if len(alts) >= 2 else 99.0
        if gap < NEAR_TIE and c[div]["t"] in [a[0] for a in alts[:2]]:
            report["near_tie_flips"] += 1
        else:
            report["errors"].append(f"{pid}: diverges at token {div} ('{b[div]['t']}' -> '{c[div]['t']}', baseline top-2 gap {gap:.3f} nats)")
    report["correct"] = not report["errors"]
    return report


def with_gpu(fn):
    with open(LOCK, "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        for _ in range(60):
            why = gpu_exclusive()
            if not why:
                break
            time.sleep(30)
        else:
            raise SystemExit(f"environment: {why}")
        return fn()


def cmd_baseline():
    wt = HERE / "baseline/TensorFold"
    if not wt.exists():
        sh(f"git -C {PROJ / 'upstream/TensorFold'} worktree add --detach {wt} {PINNED}")
    binary = build(wt, HERE / "baseline/install", HERE / "baseline/build.log")
    if not binary:
        sys.exit("baseline build failed")

    def run():
        srv = Server(binary, HERE / "baseline/server_outputs.log", drafts=False)
        try:
            outs = record_outputs(srv)
            nodraft = bench(srv, prefill=True)
        finally:
            srv.stop()
        srv = Server(binary, HERE / "baseline/server_drafts.log", drafts=True)
        try:
            drafts = bench(srv, prefill=False)
        finally:
            srv.stop()
        return outs, nodraft, drafts

    outs, nodraft, drafts = with_gpu(run)
    BASELINE.write_text(json.dumps({"commit": PINNED, "outputs": outs, "no_drafts": nodraft, "drafts": drafts}, indent=1))
    print(json.dumps({"no_drafts": nodraft, "drafts": drafts}, indent=1))


def cmd_judge(worktree: Path, tag: str):
    base = json.loads(BASELINE.read_text())
    out = PROJ / "verdicts" / f"{time.strftime('%Y%m%d-%H%M%S')}-{tag}"
    out.mkdir(parents=True)
    head = subprocess.run(f"git -C {worktree} rev-parse HEAD", shell=True, capture_output=True, text=True).stdout.strip()
    diff = subprocess.run(f"git -C {worktree} diff {PINNED} -- . ", shell=True, capture_output=True, text=True).stdout
    (out / "patch.diff").write_text(diff)
    verdict = {"tag": tag, "worktree": str(worktree), "head": head, "patch_sha256": hashlib.sha256(diff.encode()).hexdigest(),
               "patch_lines": diff.count("\n"), "time": time.strftime("%Y-%m-%dT%H:%M:%S")}

    def done(code):
        (out / "verdict.json").write_text(json.dumps(verdict, indent=1))
        print(json.dumps({k: v for k, v in verdict.items() if k not in ("correctness",)}, indent=1))
        if "correctness" in verdict:
            print("correctness:", json.dumps({k: verdict["correctness"][k] for k in ("correct", "identical", "near_tie_flips")}),
                  "errors:", verdict["correctness"]["errors"][:5])
        sys.exit(code)

    binary = build(worktree, out / "install", out / "build.log")
    if not binary:
        verdict["status"] = "build_failed"
        done(1)
    if not unit_tests(worktree, out / "tests.log"):
        verdict["status"] = "unit_tests_failed"
        done(1)

    def run():
        srv = Server(binary, out / "server_outputs.log", drafts=False)
        try:
            cand = record_outputs(srv)
            corr = compare(base["outputs"], cand)
            speed = bench(srv, prefill=True) if corr["correct"] else None
        finally:
            srv.stop()
        drafts = None
        if corr["correct"]:
            srv = Server(binary, out / "server_drafts.log", drafts=True)
            try:
                drafts = bench(srv, prefill=False)
            finally:
                srv.stop()
        # same-session baseline re-measure guards against drift (thermal, background load)
        bsrv = Server(HERE / "baseline/install/native/bin/tensorfold-native", out / "server_baseline.log", drafts=False)
        try:
            bnow = bench(bsrv, prefill=False)
        finally:
            bsrv.stop()
        return corr, speed, drafts, bnow

    try:
        corr, speed, drafts, bnow = with_gpu(run)
    except SystemExit as e:
        verdict["status"] = str(e)
        done(2)
    except Exception as e:
        verdict["status"] = f"server_error: {e}"
        done(1)
    verdict["correctness"] = corr
    # measurement-integrity guard (added 2026-10-11 16:10 after third-party GPU load inflated/deflated ratios):
    # a same-session baseline far below the recorded one, or a noisy candidate, means the GPU was shared -> retry later
    rec_base = base["no_drafts"]["decode_tok_s"]
    runs = (speed or {}).get("decode_runs") or []
    spread = (max(runs) - min(runs)) / statistics.median(runs) if runs else 0.0
    if corr["correct"] and (bnow["decode_tok_s"] < 0.97 * rec_base or spread > 0.03):
        verdict["status"] = (f"environment: GPU interference suspected (baseline now {bnow['decode_tok_s']} vs recorded "
                             f"{rec_base}, candidate spread {spread:.1%}); results not recorded as a speed - retry when the GPU is quiet")
        verdict["correctness_only"] = corr["correct"]
        done(2)
    if not corr["correct"]:
        verdict["status"] = "incorrect"
        done(1)
    verdict["status"] = "correct"
    verdict["no_drafts"] = speed
    verdict["drafts"] = drafts
    verdict["baseline_now_decode_tok_s"] = bnow["decode_tok_s"]
    verdict["speedup_decode"] = round(speed["decode_tok_s"] / bnow["decode_tok_s"], 4)
    verdict["speedup_decode_drafts"] = round(drafts["decode_tok_s"] / base["drafts"]["decode_tok_s"], 4)
    verdict["speedup_prefill"] = round(speed["prefill_tok_s"] / base["no_drafts"]["prefill_tok_s"], 4)
    done(0)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("baseline")
    j = sub.add_parser("judge")
    j.add_argument("worktree", type=Path)
    j.add_argument("--tag", default="candidate")
    a = ap.parse_args()
    if not MODEL.exists():
        sys.exit(f"missing {MODEL}: copy models/pristine there first")
    cmd_baseline() if a.cmd == "baseline" else cmd_judge(a.worktree.resolve(), a.tag)
