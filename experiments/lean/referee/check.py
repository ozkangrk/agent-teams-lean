#!/usr/bin/env python3
"""Lean referee for CS6 (Claude's code; agents must never edit referee/).

    check.py --module 'FormalConjectures.OEIS.«358684»' --theorem OeisA358684.a_7 --proof PATH/Proof.lean [--timeout 1200]

The submission is a Lean file that imports the upstream module and declares a top-level `theorem swarm_proof` (proves the
statement) or `theorem swarm_disproof` (proves its negation, e.g. by a counterexample).
Acceptance requires all of:
1. Static scan: no metaprogramming, unsafe code, options that weaken checking, or custom axioms (see FORBIDDEN).
2. The submission compiles (as its own module) in a sandbox: no network, read-only toolchain and upstream project,
   writable scratch only.
3. A separate check file, `theorem __referee_check : type_of% @<theorem> := swarm_proof`, compiles. The target type
   comes from the **upstream compiled constant**, so a submission cannot change the statement, its definitions or
   its instances.
4. `#print axioms __referee_check` lists only propext, Classical.choice and Quot.sound. This rejects sorryAx,
   native_decide (Lean.ofReduceBool / trustCompiler) and any custom axiom.
Prints one JSON verdict line.
"""
import argparse, json, os, re, shutil, subprocess, sys, tempfile, time
from pathlib import Path

UP = Path.home() / "Desktop/research/10-swarm-lean/upstream/formal-conjectures"
ELAN = Path.home() / ".elan"
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [
    r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\bunsafe\b", r"implemented_by", r"@\[\s*extern", r"\bopaque\b",
    r"set_option\s+(?!maxHeartbeats\b|maxRecDepth\b|synthInstance\.maxHeartbeats\b|linter\.)", r"debug\.",
    r"\bmacro\b", r"\bmacro_rules\b", r"\bsyntax\b", r"\belab\b", r"\belab_rules\b", r"\bnotation\b",
    r"\binfix[lr]?\b", r"\bprefix\b", r"\bpostfix\b", r"#eval", r"\brun_cmd\b", r"\brun_elab\b", r"\brun_meta\b",
    r"\binitialize\b", r"builtin_initialize", r"\bLean\.Elab\b", r"\bLean\.Meta\b", r"\bLean\.Environment\b",
    r"\baddDecl\b", r"\bIO\.", r"\bSystem\.", r"native_decide", r"decide\s*\+\s*native", r"\bofReduceBool\b",
    r"\btrustCompiler\b", r"#exit", r"\bimport\s+Lean\b",
]


def verdict(ok, **kw):
    print(json.dumps({"accepted": ok, **kw}))
    sys.exit(0 if ok else 1)


def strip_comments(src):
    src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    return re.sub(r"--[^\n]*", " ", src)


def sandbox(cmd, scratch, timeout, env):
    bw = ["bwrap", "--die-with-parent", "--new-session", "--unshare-all", "--ro-bind", "/usr", "/usr",
          "--ro-bind", "/lib", "/lib", "--ro-bind-try", "/lib64", "/lib64", "--ro-bind", "/bin", "/bin",
          "--ro-bind", "/etc", "/etc", "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
          "--ro-bind", str(ELAN), str(ELAN), "--ro-bind", str(UP), str(UP), "--bind", str(scratch), str(scratch),
          "--chdir", str(scratch)]
    for x in filter(None, os.environ.get("REFEREE_EXTRA_LEAN_PATH", "").split(":")):  # self-test only
        bw[-2:-2] = ["--ro-bind", x, x]
    return subprocess.run(bw + cmd, capture_output=True, text=True, timeout=timeout, env=env)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--module", required=True); ap.add_argument("--theorem", required=True)
    ap.add_argument("--proof", required=True); ap.add_argument("--timeout", type=int, default=1200)
    a = ap.parse_args()
    src = Path(a.proof).read_text()
    body = strip_comments(src)
    bad = sorted({p for p in FORBIDDEN if re.search(p, body)})
    if bad:
        verdict(False, stage="static", why=f"forbidden constructs: {bad}")
    has_p = bool(re.search(r"^\s*theorem\s+swarm_proof\b", body, re.M))
    has_d = bool(re.search(r"^\s*theorem\s+swarm_disproof\b", body, re.M))
    if has_p == has_d:
        verdict(False, stage="static", why="declare exactly one of top-level `theorem swarm_proof` / `theorem swarm_disproof`")
    if re.search(r"^\s*(namespace|section)\b", body, re.M) and not re.search(r"^\s*end\b", body, re.M):
        verdict(False, stage="static", why="unclosed namespace/section")
    extra = os.environ.get("REFEREE_EXTRA_LEAN_PATH", "")  # self-test only
    lean_path = subprocess.run([str(ELAN / "bin/lake"), "env", "printenv", "LEAN_PATH"], cwd=UP,
                               capture_output=True, text=True, timeout=120).stdout.strip()
    lean = str(next((ELAN / "toolchains").glob("leanprover--lean4---v4.33.1*")) / "bin/lean")
    with tempfile.TemporaryDirectory(prefix="cs6ref-") as td:
        td = Path(td)
        shutil.copy(a.proof, td / "Submission.lean")
        env = {"PATH": "/usr/bin:/bin", "HOME": str(td), "LEAN_PATH": f"{lean_path}:{td}" + (f":{extra}" if extra else ""), "LANG": "C.UTF-8"}
        t0 = time.time()
        try:
            r1 = sandbox([lean, "-o", str(td / "Submission.olean"), "-i", str(td / "Submission.ilean"),
                          str(td / "Submission.lean")], td, a.timeout, env)
        except subprocess.TimeoutExpired:
            verdict(False, stage="compile", why=f"timeout {a.timeout}s")
        if r1.returncode != 0 or not (td / "Submission.olean").exists():
            verdict(False, stage="compile", why=(r1.stdout + r1.stderr)[-1500:])
        target = f"type_of% @{a.theorem}" if has_p else f"¬ (type_of% @{a.theorem})"
        (td / "Check.lean").write_text(f"import Submission\nimport {a.module}\n\n"
                                       f"theorem __referee_check : {target} := {'swarm_proof' if has_p else 'swarm_disproof'}\n"
                                       f"#print axioms __referee_check\n")
        try:
            r2 = sandbox([lean, str(td / "Check.lean")], td, a.timeout, env)
        except subprocess.TimeoutExpired:
            verdict(False, stage="check", why=f"timeout {a.timeout}s")
        out = r2.stdout + r2.stderr
        if r2.returncode != 0 or "error" in out.lower():
            verdict(False, stage="check", why=out[-1500:])
        m = re.search(r"depends on axioms:\s*\[([^\]]*)\]", out)
        axioms = {x.strip() for x in m.group(1).split(",")} if m else set()
        if not m and "does not depend on any axioms" not in out:
            verdict(False, stage="axioms", why="no axiom report: " + out[-500:])
        if not axioms <= STD_AXIOMS:
            verdict(False, stage="axioms", why=f"non-standard axioms: {sorted(axioms - STD_AXIOMS)}")
        verdict(True, kind="proof" if has_p else "disproof", module=a.module, theorem=a.theorem, axioms=sorted(axioms), seconds=round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
