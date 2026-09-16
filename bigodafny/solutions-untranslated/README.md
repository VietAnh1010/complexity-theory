# `solutions-untranslated/` — a decision, not a backlog

4 rows that will not be translated. Each file carries its blocker in place of a
body and no stub, so re-running `scaffold.py` never regenerates one. They stay
here so every one of the 640 dataset rows has a file.

| rows | blocker |
|---|---|
| `967/967_5.dfy`, `967/967_19.dfy`, `3079/3079_181.dfy`, `3079/3079_85.dfy` | all four `print()` a bare Python float |

Matching a bare `print(float)` byte-for-byte needs two things at once:
bit-exact IEEE-754 arithmetic — Dafny's `real` is an exact rational and does not
round where a float rounds — **and** CPython's shortest-round-trip `repr`.

Both gates compare stdout as text, so for these rows `validate.py` and
`difftest.py` are *inapplicable*, not merely failing. That distinction is the
whole point of the directory: a row that cannot be judged is recorded as such
rather than counted as a failure.

The same problem **with a format spec is tractable**, and one row proves it:
`solutions/2496/2496_30.dfy` computes in exact rationals and hand-writes
`FormatG9` to replicate `'{:.9}'.format(x)`, agreeing on all 42 comparable
tests. It is bare `print(float)` that has no finite specification.
