"""Build the agent prompt for one batch. Committed so a run is reproducible.

Shaped after the prompt that carried the translation waves in this project:
the concision skill first, the working directory and PATH stated once, the
contract, the gate, then the rules that previous waves proved were needed.

The two arms differ in exactly one paragraph. Everything else -- guide,
prelude, description, Python, the rules, the reporting format -- is identical,
so the label is the only variable between them.

    python3 experiments/prompts.py --arm blind --run-id pilot1 --sids 5_100 ...
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from stage import CX_ROOT                                          # noqa: E402

COMMON = """FIRST ACTION: call the Skill tool with skill="my-concise". Follow it for all
prose. Dafny and JSON are exempt.

# Task

You have {n} examples. Each is a self-contained directory:

{dirs}

Work them ONE AT A TIME, in the order listed -- they are ordered easiest
first. In each directory read TASK.md first, then GUIDE.md, then
description.md, solution.py and task.dfy.

Start every Bash call that runs dafny with:
    export PATH="$PATH:/root/.dotnet/tools"

Verify with, from inside the example directory:
    dafny verify task.dfy --solver-path /usr/local/bin/z3 \\
        --verification-time-limit 60 --error-limit 0

Only `verifier finished with N verified, 0 errors` is a pass. `grep -q "0
errors"` would also match "10 errors" -- read the number. A lemma reported as
timed out proves nothing even when its callers report verified.

`task.dfy` already verifies as given. Your additions are what can break it.

Run every dafny call in the FOREGROUND and wait for it. Do not background a
verification, do not set a Monitor on one, and never end your turn waiting for
something. The pilot lost three of its four examples that way.

# What counts

{arm_para}

# Hard rules

- Change NO executable code. Only ghost declarations, `steps` assignments,
  `invariant`, `decreases`, `ensures`, `requires`, and `lemma`s. The grader
  compiles your file and the original and compares the emitted control flow; a
  bound made true by changing the algorithm is rejected, and it is the failure
  this experiment most wants to catch.
- NEVER `assume`, including `assume {{:axiom}}`. It silences an obligation
  instead of discharging it and still reports 0 errors. An unfinished proof
  scores better than a hollow one.
- Read and write NOTHING outside your example directories. Do not run git. Do
  not invoke any bigodafny skill. This is enforced, not requested: a
  containment hook denies those calls and logs every attempt, and an example
  whose agent attempted one is thrown out of the results.
- Add a `requires` only if the problem statement in description.md actually
  says it. Every clause you add is checked against this row's real stored
  inputs, and one that excludes an input the row answers fails the example. A
  bound bought by narrowing the problem is not a bound.
- Constants are free. `steps <= 7 * n + 12` establishes linear. Do not tune
  them; tuning wastes the run.

# result.json first, then the proof

Your FIRST act in each directory, before any proof work, is to write its
`result.json` with `verdict: "gave_up"` and the fields TASK.md names. Then
update it as you learn more. Written that way, an example you run out of
budget on is still recorded; written afterwards, it is lost. Follow
`RESULT.schema.json` exactly; `verdict` must be one of `proves`, `refutes`,
`gave_up`.

BUDGET, and it is hard: about 20 tool calls per example, 25 at the very most.
When you hit it, set `verdict: "gave_up"`, record in `notes` what the obstacle
was -- which obligation, which invariant you could not find -- and MOVE ON to
the next example. A precise give-up is data. Four give-ups are a result; one
polished proof and three untouched examples is not.

The examples are ordered easiest first. If you are still on the first one after
25 calls, you are over budget for it -- write it off and go.

# Report

One line per example: id, verdict, the bound you proved, and for a give-up the
obstacle in six words. Then one line on anything you noticed across the batch.
"""

LABELED = """`task.dfy`'s header states the cost claimed for this method. Prove a bound of
that shape with a ghost step counter.

If the claim is wrong, prove the bound that is actually true and set `verdict`
to `refutes`. Do not bend a proof to fit the claim -- a claim shown false is
worth more here than a claim restated. Two claims in this corpus have already
been disproved this way."""

BLIND = """The cost of this method is NOT stated anywhere, and you will not find it. Your
job has two halves and the order matters.

FIRST: read the code and commit to a class. Write `result.json` with `guess`
and `guess_basis` filled in and every other field null, BEFORE you attempt any
proof. The experiment measures whether the guess was right, so a guess written
after the proof measures nothing.

THEN: prove your guess with a ghost step counter. If the proof forces you to a
different bound, leave `guess` exactly as written, record what you proved in
`proved_class`, and set `verdict` to `refutes`."""


def build(arm, run_id, sids):
    root = CX_ROOT / run_id / arm
    dirs = "\n".join(f"    {root / s}" for s in sids)
    return COMMON.format(n=len(sids), dirs=dirs,
                         arm_para=LABELED if arm == "labeled" else BLIND)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--arm", choices=["labeled", "blind"], required=True)
    ap.add_argument("--run-id", required=True)
    ap.add_argument("--sids", nargs="+", required=True)
    a = ap.parse_args()
    print(build(a.arm, a.run_id, a.sids))


if __name__ == "__main__":
    main()
