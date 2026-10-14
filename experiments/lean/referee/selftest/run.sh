#!/usr/bin/env bash
# Referee self-test (Claude's): one good proof must be accepted; six cheating attempts must be rejected.
cd "$(dirname "$0")"; M="FormalConjectures.OEIS.«358684»"; fail=0
for t in good:a_5:true sorry:a_7:false mismatch:a_7:false usesorry:a_7:false native:a_6:false axiom:a_7:false skip:a_7:false; do
  IFS=: read f th want <<< "$t"
  out=$(python3 -I ../check.py --module "$M" --theorem OeisA358684.$th --proof "$PWD/$f.lean")
  got=$(echo "$out" | python3 -c 'import json,sys; print(str(json.loads(sys.stdin.read())["accepted"]).lower())')
  [ "$got" = "$want" ] && echo "PASS $f" || { echo "FAIL $f: $out"; fail=1; }
done
# disproof path (fake upstream module compiled locally; REFEREE_EXTRA_LEAN_PATH is honoured only for self-tests)
T="$PWD/fakeup"
for t in disproof_ok:fake_false:true disproof_bad:fake_true:false both:fake_true:false; do
  IFS=: read f th want <<< "$t"
  out=$(REFEREE_EXTRA_LEAN_PATH="$T" python3 -I ../check.py --module FakeUp --theorem $th --proof "$PWD/$f.lean")
  got=$(echo "$out" | python3 -c 'import json,sys; print(str(json.loads(sys.stdin.read())["accepted"]).lower())')
  [ "$got" = "$want" ] && echo "PASS $f" || { echo "FAIL $f: $out"; fail=1; }
done
exit $fail
