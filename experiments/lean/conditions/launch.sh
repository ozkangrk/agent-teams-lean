#!/usr/bin/env bash
# Launch one CS6 condition in tmux, inside:
#   - a memory scope (MemoryHigh=MEMMAX, default 24G; MemoryMax=MEMMAX+8G; no swap; OOMPolicy=continue)
#   - pinned to CPUS
# Agent tool calls run in the kernel sandbox: no network, only this workspace visible among work/*, and
# referee/, tools/, upstream/ and the toolchain read-only.
set -euo pipefail
C="$1"; HOURS="$2"; CPUS="$3"; PROBS="${4:-pilot.jsonl}"
P="$HOME/Desktop/research/10-swarm-lean"; W="$P/work/$C"; SOCK="/tmp/pa-cs6-$C.sock"; G="$HOME/Desktop/research/_gates"
[ -e "$W" ] && { echo "$W exists: refusing to reuse a condition workspace"; exit 1; }
mkdir -p "$W/proofs"; [ -f "$P/conditions/TASK.$C.md" ] && cp "$P/conditions/TASK.$C.md" "$W/TASK.md" || cp "$P/conditions/TASK.md" "$W/"; cp "$P/conditions/AGENTS.$C.md" "$W/AGENTS.md"; cp "$P/conditions/$PROBS" "$W/PROBLEMS.jsonl"; : > "$W/ledger.jsonl"
date +%s > "$W/.launched"; echo "$HOURS" > "$W/.budget_hours"; echo "$CPUS" > "$W/.cpus"
echo "$(date -Iseconds) launch $C hours=$HOURS cpus=$CPUS problems=$PROBS" >> "$P/conditions/launches.log"
MEMHI="${MEMMAX:-24}"; MEMMX=$((MEMHI + 8))
GATE="python3 -I $G/cs6_gate.py $W"
cat > "$W/.run.sh" <<RUN
#!/usr/bin/env bash
export PRIME_AGENT_KERNEL_PYTHON="$G/kernel_sandbox.sh" SANDBOX_HIDE="$P/work" SANDBOX_KEEP="$W" SANDBOX_RO="$P/referee:$P/tools:$P/upstream:$P/library:$HOME/.elan:$G" SANDBOX_OVERLAY="${OVERLAY:-}"
MSG="TASK.md, AGENTS.md ve PROBLEMS.jsonl dosyalarini oku ve gorevi yurut. Zaman butcen ${HOURS} saat; butce dolana kadar calis, her denemeyi ledger.jsonl dosyasina kaydet, sonunda RESULT.md dosyasini yaz."
exec systemd-run --user --scope -q --unit=cs6-$C-\$(date +%s) -p MemoryHigh=${MEMHI}G -p MemoryMax=${MEMMX}G -p MemorySwapMax=0 -p OOMPolicy=continue -- taskset -c $CPUS prime-agent --daemon-socket $SOCK --thinking high --goal "CS6 $C: Lean kanitlari" -- "\$MSG"
RUN
chmod +x "$W/.run.sh"
# tmux server, supervisor and watchdog run in their own systemd units, so they survive a Claude app restart (CS6 D3)
TS=$(date +%s)
systemd-run --user --scope -q --unit="tmux-research-$C-$TS" -- tmux -L research new-session -d -s "cs6-$C" -x 220 -y 60 -c "$W" "$W/.run.sh; echo EXITED; sleep 86400"
DEADLINE=$(( $(cat "$W/.launched") + HOURS * 3600 ))
systemd-run --user -q --setenv=PATH="$PATH" --unit="sup-cs6-$C-$TS" -p StandardOutput=append:"$W/supervisor.out" -p StandardError=append:"$W/supervisor.out" python3 -I "$G/supervisor.py" --workdir "$W" --tmux "cs6-$C" --tmux-socket research --deadline "$DEADLINE" --socket "$SOCK" --nudge-gate "$GATE" --precheck-min 30
systemd-run --user -q --setenv=PATH="$PATH" --unit="wd-cs6-$C-$TS" -p StandardOutput=append:"$W/watchdog.out" -p StandardError=append:"$W/watchdog.out" python3 -I "$G/watchdog.py" --workdir "$W" --socket "$SOCK" --until "$(( DEADLINE + 900 ))" --limit-min 20
echo "launched cs6-$C (tmux -L research) in $W on cpus $CPUS (daemon $SOCK), sandboxed kernel"
