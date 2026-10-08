# BigODafny

BigODafny is a Python-to-Dafny translation corpus built from BigO(Bench)'s
`time_complexity_test_set`. It contains 640 competitive-programming solutions.
Each row keeps the complexity label inferred by BigO(Bench) for the original
Python program.

Read [DOCS.md](DOCS.md) before working on the corpus. It explains the current
state, the status directories, the gates, and which documents are authoritative.

## What a row contains

Most source solutions are stdin scripts, not functions. BigO(Bench) supplies an
`Input` dataclass for each problem; BigODafny turns that dataclass into the
Dafny entry point:

```dafny
method Solve(n: int, a_list: seq<int>) returns (output: string)
```

`signature.py` performs that conversion. It maps 309 of 311 problems. The two
unmappable dataclasses use an untyped `list`, so the project records them as
unmappable instead of guessing an element type.

## Behaviour checking

The normal harness compiles a Dafny row to Python, calls `Solve` with values
created by BigO(Bench)'s own `Input.from_str`, and compares stdout.

```text
stored input -> Input.from_str -> Solve(...) -> translated Python stdout
                                         |
                                   compare with stored output
```

There are two behaviour tiers:

| Tier | Rows | Check |
|---|---:|---|
| `strict` | 540 | Compare against the stored output. |
| `loose` | 100 | Compare the Dafny translation with the original Python. |

The split is empirical: only 540 original Python programs reproduce the stored
output byte-for-byte. The other 100 often have multiple accepted outputs, so a
byte comparison would reject the original program itself.

## Current corpus shape

The seven status directories partition the 640 rows:

| Directory | Rows | Meaning |
|---|---:|---|
| `solutions/` | 291 | Behaviour-gated, safety-verified, and label-screened. |
| `solutions-unscreened/` | 127 | Behaviour-gated but not label-audited. |
| `solutions-disputed/` | 202 | The audit found a label or translation concern. |
| `solutions-unsure/` | 8 | Gated and verified; the label audit could not decide. |
| `solutions-ungateable/` | 5 | The normal behaviour gate cannot reach a reliable verdict. |
| `solutions-unverified/` | 3 | Behaviour-gated, but Dafny cannot prove safety or termination. |
| `solutions-untranslated/` | 4 | Bare-float output has no practical exact Dafny specification. |

`solutions-proved/` is an overlay, not an eighth status. It contains 321
instrumented copies with machine-checked complexity bounds.

## Repository map

| Path | Purpose |
|---|---|
| `solutions*/` | Dafny corpus, grouped by current status. |
| `prelude.dfy` | Shared helpers used by translations and proofs. |
| `data/` | Generated corpus state, gate results, and analysis records. |
| `batches/` | Campaign manifests, prompts, trajectories, and audit evidence. |
| `COMPLEXITY.md` | The stipulated cost model and proof approach. |

## Toolchain

The repository uses Dafny 4.11.0 and Z3 4.12.1. Typical commands are:

```bash
# dafny and z3 on PATH
# the build, in order
python3 extract.py          # download BigOBench -> data/tasks.jsonl
python3 signature.py        # dataclass -> Dafny Solve signatures
python3 scaffold.py         # .dfy stubs; never overwrites a real body
python3 baseline.py         # original Python vs its own tests (--workers N)
python3 dataset.py          # join everything -> dataset.jsonl, stats.json
# gates
python3 selftest.py         # validate.py must report a wrong answer as fail, a build error as build
python3 validate.py --only 1053_38
python3 difftest.py --loose
python3 proofs.py
# derived data, after any change to the corpus
python3 callgraph.py        # call depth per row -> data/call_depth.jsonl
python3 collect.py          # everything above, plus size and loop profile -> out/artifact_data.json
```

The complexity model is intentionally not a measurement of Dafny's Python
backend. It is a stipulated, implementation-independent model described in
[COMPLEXITY.md](COMPLEXITY.md).
