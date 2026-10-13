# `solutions-untranslated/`: will not be translated

Rows set aside on purpose. Each file states its blocker and has no stub, so
`scaffold.py` never recreates one. They stay so every row has a file.

| Rows | Blocker |
|---|---|
| `967/967_5.dfy`, `967/967_19.dfy`, `3079/3079_181.dfy`, `3079/3079_85.dfy` | each prints a bare Python float |

Matching a bare `print(float)` needs IEEE-754 rounding (Dafny's `real` is an
exact fraction) and CPython's shortest-digits `repr`. So neither gate can
judge these rows, and they are not counted as failures.

A float printed **with a format spec** is doable: `solutions/2496/2496_30.dfy`
uses exact fractions and a hand-written `FormatG9`, and agrees on all 42
comparable tests.
