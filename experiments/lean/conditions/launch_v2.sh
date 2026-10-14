#!/usr/bin/env bash
# Launch one Lean condition (CS8 onwards; Claude's). Differences from launch.sh (CS6/CS7):
#   - allow-list kernel sandbox (kernel_sandbox_v2.sh) with a per-condition Prime Agent session directory
#     (agent-sessions/<C>), so no agent can read another condition's logs, earlier results or the experimenter's files
#   - daemon socket under /run/user/$UID (hidden from kernels)
#   - supervisor runs as a transient *scope* (the referee's bwrap fails inside a user *service*; CS7 D6) and stops the
#     agent daemon unit after the session is closed
#   - optional SLICE: several conditions share one memory budget (CS8: four independent agents in one 20G/28G slice)
# Usage: [MEMMAX=20] [SLICE=name.slice] [OVERLAY=...] launch_v2.sh EXP C HOURS CPUS PROBLEMS AGENTS_FILE TASK_FILE
set -euo pipefail
EXP="$1"; C="$2"; HOURS="$3"; CPUS="$4"; PROBS="$5"; AGENTS="$6"; TASKF="$7"
P="$HOME/Desktop/research/10-swarm-lean"; W="$P/work/$C"; G="$HOME/Desktop/research/_gates"
SESS="$P/agent-sessions/$C"; SOCK="/run/user/$(id -u)/pa-$EXP-$C.sock"
[ -e "$W" ] && { echo "$W exists: refusing to reuse a condition workspace"; exit 1; }
mkdir -p "$W/proofs" "$SESS/sessions"
cp "$P/conditions/$TASKF" "$W/TASK.md"; cp "$P/conditions/$AGENTS" "$W/AGENTS.md"; cp "$P/conditions/$PROBS" "$W/PROBLEMS.jsonl"; : > "$W/ledger.jsonl"
date +%s > "$W/.launched"; echo "$HOURS" > "$W/.budget_hours"; echo "$CPUS" > "$W/.cpus"
echo "$(date -Iseconds) launch $EXP $C hours=$HOURS cpus=$CPUS problems=$PROBS agents=$AGENTS task=$TASKF slice=${SLICE:-none} sandbox=v2" >> "$P/conditions/launches.log"
MEMHI="${MEMMAX:-20}"; MEMMX=$((MEMHI + 8)); TS=$(date +%s); UNIT="$EXP-$C-$TS"
SLICEARG=""; [ -n "${SLICE:-}" ] && SLICEARG="--slice=$SLICE"
cat > "$W/.run.sh" <<RUN
#!/usr/bin/env bash
export PRIME_AGENT_KERNEL_PYTHON="$G/kernel_sandbox_v2.sh" PRIME_AGENT_SESSION_DIR="$SESS/sessions"
export SANDBOX_KEEP="$W" SANDBOX_SESS="$SESS" SANDBOX_RO="$P/referee:$P/tools:$P/upstream:$P/library" SANDBOX_OVERLAY="${OVERLAY:-}"
MSG="TASK.md, AGENTS.md ve PROBLEMS.jsonl dosyalarini oku ve gorevi yurut. Zaman butcen ${HOURS} saat; butce dolana kadar calis, her denemeyi ledger.jsonl dosyasina kaydet, sonunda RESULT.md dosyasini yaz."
exec systemd-run --user --scope -q --unit=$UNIT $SLICEARG -p MemoryHigh=${MEMHI}G -p MemoryMax=${MEMMX}G -p MemorySwapMax=0 -p OOMPolicy=continue -- taskset -c $CPUS prime-agent --daemon-socket $SOCK --thinking high --goal "$EXP $C: Lean kanitlari" -- "\$MSG"
RUN
chmod +x "$W/.run.sh"
systemd-run --user --scope -q --unit="tmux-research-$C-$TS" -- tmux -L research new-session -d -s "$EXP-$C" -x 220 -y 60 -c "$W" "$W/.run.sh; echo EXITED; sleep 86400"
DEADLINE=$(( $(cat "$W/.launched") + HOURS * 3600 ))
GATE="python3 -I $G/cs6_gate.py $W"
setsid nohup systemd-run --user --scope -q --unit="sup-$EXP-$C-$TS" -- python3 -I "$G/supervisor.py" --workdir "$W" --tmux "$EXP-$C" --tmux-socket research \
  --deadline "$DEADLINE" --socket "$SOCK" --nudge-gate "$GATE" --precheck-min 30 --stop-unit "$UNIT.scope" >> "$W/supervisor.out" 2>&1 < /dev/null &
systemd-run --user -q --setenv=PATH="$PATH" --unit="wd-$EXP-$C-$TS" -p StandardOutput=append:"$W/watchdog.out" -p StandardError=append:"$W/watchdog.out" \
  python3 -I "$G/watchdog.py" --workdir "$W" --socket "$SOCK" --until "$(( DEADLINE + 900 ))" --limit-min 20
echo "launched $EXP-$C in $W on cpus $CPUS (daemon $SOCK, sessions $SESS, unit $UNIT)"
