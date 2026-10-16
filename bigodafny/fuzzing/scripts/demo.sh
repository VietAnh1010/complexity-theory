#!/usr/bin/env bash
# Run deghost and annotate on one row; write inputs and outputs to demo/<problem>/.
#   scripts/demo.sh SID [--run] [enable=functions,seq,arrays]
# deghost runs on the row's proof copy (solutions-proved/), annotate on the
# row itself; a missing input skips that pass. --run also runs steptrace.py on
# both, keeping each one's summary. Other options go to annotate.
set -euo pipefail
cd "$(dirname "$0")/.."                       # fuzzing/
sid=${1:?usage: scripts/demo.sh SID [--run] [enable=functions,seq,arrays]}
shift
run=
options=()
for a in "$@"; do
  if [[ $a == --run ]]; then run=--run; else options+=("$a"); fi
done
pid=${sid%%_*}
out=demo/$pid
tool=DafnySteps/bin/Release/net10.0/DafnySteps
python="../.venv/bin/python3 -u"             # -u: stdout and stderr stay in order

if ! log=$(dotnet build -c Release DafnySteps -nologo 2>&1); then
  echo "$log"; exit 1
fi
proof=$(ls ../solutions-proved/$pid/$sid.dfy ../solutions-proved/value-bounded/$pid/$sid.dfy 2>/dev/null | head -1 || true)
plain=$(find ../solutions* -path ../solutions-proved -prune -o -name "$sid.dfy" -print | head -1)
if [[ -z $proof && -z $plain ]]; then
  echo "no row and no proof copy named $sid" >&2; exit 1
fi
mkdir -p "$out"

if [[ -n $proof ]]; then
  echo "deghost   $proof"
  cp "$proof" "$out/$sid.proof.dfy"
  $tool deghost "$proof" "$out/$sid.deghost.dfy" trace contracts points="$out/$sid.points.json"
else
  echo "deghost   skipped: no proof copy of $sid"
fi

if [[ -n $plain ]]; then
  echo "annotate  $plain"
  cp "$plain" "$out/$sid.plain.dfy"
  $tool annotate "$plain" "$out/$sid.annotate.dfy" "${options[@]}"
  dafny resolve "$out/$sid.annotate.dfy" | tail -1
else
  echo "annotate  skipped: no row $sid"
fi

if [[ $run == --run ]]; then
  if [[ -n $proof ]]; then
    $python steptrace.py "$sid" > "$out/$sid.trace.proof.txt" 2>&1
    echo "steptrace proof:    $(tail -1 "$out/$sid.trace.proof.txt")"
  fi
  if [[ -n $plain ]]; then
    $python steptrace.py "$sid" --dfy "$out/$sid.annotate.dfy" > "$out/$sid.trace.annotate.txt" 2>&1
    echo "steptrace annotate: $(tail -1 "$out/$sid.trace.annotate.txt")"
  fi
fi
echo "-> $out/"
