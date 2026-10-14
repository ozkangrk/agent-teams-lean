#!/usr/bin/env bash
# Prime Agent kernel wrapper (Claude's). Set PRIME_AGENT_KERNEL_PYTHON to this script. Every agent tool call (python,
# bash, background shells) then runs with no network and sees only its own condition workspace:
#   SANDBOX_HIDE=<dir>  directory hidden behind an empty tmpfs (all condition workspaces)
#   SANDBOX_KEEP=<dir>  directory re-exposed read-write (this condition's workspace)
#   SANDBOX_RO=<a:b:..> directories forced read-only (referee, upstream statements and builds, toolchain)
#   SANDBOX_OVERLAY="src=dst;src2=dst2"  read-only views mounted over dst (e.g. leak-free sanitized sources)
# Always: no network, private PID namespace, and the tmux and user-bus socket directories hidden (CS7 D6).
args=(--dev-bind / / --unshare-net --unshare-pid --proc /proc --die-with-parent)
# CS7 D6: the escape went through the tmux socket and the user's systemd/D-Bus sockets, and a same-uid kill reached the
# supervisor. Hide /tmp/tmux-$UID and /run/user/$UID and use a private PID namespace (harness processes are invisible).
for d in "/tmp/tmux-$(id -u)" "/run/user/$(id -u)"; do [ -d "$d" ] && args+=(--tmpfs "$d"); done
[ -n "$SANDBOX_HIDE" ] && args+=(--tmpfs "$SANDBOX_HIDE")
[ -n "$SANDBOX_KEEP" ] && args+=(--bind "$SANDBOX_KEEP" "$SANDBOX_KEEP")
IFS=: read -ra RO <<< "${SANDBOX_RO:-}"; for d in "${RO[@]}"; do [ -n "$d" ] && args+=(--ro-bind "$d" "$d"); done
IFS=";" read -ra OV <<< "${SANDBOX_OVERLAY:-}"; for pr in "${OV[@]}"; do [ -n "$pr" ] && args+=(--ro-bind "${pr%%=*}" "${pr#*=}"); done
exec bwrap "${args[@]}" -- "$HOME/.prime/agent/kernel-venv/bin/python" "$@"
