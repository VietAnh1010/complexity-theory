# `solution-guessed-verified/`

Proof attempts written by **blind-arm** agents in the complexity experiment
(`experiments/`). Each file is one agent's instrumented copy of a row, produced
without ever seeing BigOBench's complexity label.

The name is the contrast with its sibling:

| directory | the label was |
|---|---|
| `solutions-verified/` | **known** to whoever wrote the proof |
| `solution-guessed-verified/` | **withheld**; the agent committed to a class in writing first |

## How a file gets here

`experiments/archive_attempts.py --run-id <run>`, run after grading. Agents do
not write here and must not: `guard.py` confines them to their own example
directory while a run is armed, and an example whose agent reached into the
repository is discarded from the results. The label is in plain text throughout
this repository, so that containment is what makes the blind arm's accuracy
mean anything. Archiving is a post-hoc step run by the unconfined main session.

Only a **modified** `task.dfy` is archived. An untouched file is the staged
original, not an attempt.

## What each file carries

A provenance header with the agent's predicted class, the basis it wrote down
*before* proving, the bound it proved, its verdict, the reference label, and
whether every gate passed. The body is verbatim except the prelude `include`,
rewritten so the file verifies from this directory rather than from the staged
example directory.

## Reading the `prediction correct` field

A prediction scored incorrect is not necessarily a misreading. The label was
measured on the **Python**; these files are the **Dafny**. Where a translation
artifact moves the complexity class — a sequence functional update in a loop is
O(1) in CPython and a full copy in Dafny — the two disagree by construction and
the agent is scored against a program it was not given. `1039_15` is the worked
case: predicted `O(n**2)`, proved `O(n**2)`, scored incorrect against
`O(nlogn)`, and the agent named the cause itself.

## Status of this directory

These are **not** dataset rows. They are not gated by `validate.py`, are not
counted in `stats.json`, and are not part of `solutions/`. They are the
experiment's primary artifact, kept because the run directories live in a
per-session scratch path and do not survive the container.

15 attempts from run `pilot1`; zero contain `assume`.
