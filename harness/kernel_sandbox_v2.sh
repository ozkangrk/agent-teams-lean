#!/usr/bin/env bash
# Prime Agent kernel wrapper, allow-list version (Claude's; CS8 onwards). Set PRIME_AGENT_KERNEL_PYTHON to this script.
# Every agent tool call then runs in a fresh root that contains ONLY:
#   /usr (with /bin /lib /sbin links), /etc, private /proc /dev /tmp /run, the kernel's Python (read-only),
#   the Lean toolchain ~/.elan (read-only), and
#   SANDBOX_KEEP=<dir>   this condition's workspace (read-write)
#   SANDBOX_SESS=<dir>   this condition's own Prime Agent session directory (read-write; kernel state snapshots)
#   SANDBOX_RO=<a:b:..>  read-only directories (referee, tools, upstream builds, library)
#   SANDBOX_OVERLAY="src=dst;..."  read-only views mounted over dst (leak-free sanitized sources)
# Everything else under $HOME is absent: other workspaces, earlier experiments' results and logs, the paper, agent
# session logs and secrets, and the experimenter's files. No network, private PID/IPC/UTS namespaces, so harness
# processes, the tmux server and the user bus are unreachable (CS7 D6, D8).
H="$HOME"
# In the private PID namespace the worker's host pid does not exist, so the kernel's owner check
# (PRIME_AGENT_KERNEL_OWNER_PID) would see its owner as dead and exit; without it the kernel watches its parent (the
# namespace init), and --die-with-parent still ends it with the worker. The orphan journal would hold namespace pids.
args=(--unshare-net --unshare-pid --unshare-ipc --unshare-uts --die-with-parent
      --unsetenv PRIME_AGENT_KERNEL_OWNER_PID --unsetenv PRIME_AGENT_INTERNAL_ORPHAN_PROCESS_JOURNAL
      --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/sbin /sbin
      --ro-bind /etc /etc --proc /proc --dev /dev --tmpfs /dev/shm --tmpfs /tmp --tmpfs /run
      --tmpfs /home --dir "$H"
      --ro-bind "$H/.local/share/uv/python" "$H/.local/share/uv/python"
      --ro-bind "$H/.prime/agent/kernel-venv" "$H/.prime/agent/kernel-venv"
      --ro-bind "$H/.local/share/prime-agent" "$H/.local/share/prime-agent"
      --ro-bind "$H/.elan" "$H/.elan")
[ -d /lib64 ] && args+=(--ro-bind /lib64 /lib64)
IFS=: read -ra RO <<< "${SANDBOX_RO:-}"; for d in "${RO[@]}"; do [ -n "$d" ] && args+=(--ro-bind "$d" "$d"); done
IFS=";" read -ra OV <<< "${SANDBOX_OVERLAY:-}"; for pr in "${OV[@]}"; do [ -n "$pr" ] && args+=(--ro-bind "${pr%%=*}" "${pr#*=}"); done
[ -n "$SANDBOX_SESS" ] && args+=(--bind "$SANDBOX_SESS" "$SANDBOX_SESS")
[ -n "$SANDBOX_KEEP" ] && args+=(--bind "$SANDBOX_KEEP" "$SANDBOX_KEEP" --chdir "$SANDBOX_KEEP")
exec bwrap "${args[@]}" -- "$H/.prime/agent/kernel-venv/bin/python" "$@"
