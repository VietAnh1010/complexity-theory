# BigODafny

Python solutions to competitive-programming problems, translated into Dafny.
They come from BigOBench's `time_complexity_test_set`; each keeps BigOBench's
complexity label for the original Python. Read [DOCS.md](DOCS.md) before
changing anything; it defines the project's terms.

## A row

Each problem's `Input` dataclass becomes the Dafny entry point
(`signature.py`):

```dafny
method Solve(n: int, a_list: seq<int>) returns (output: string)
```

The harness compiles the Dafny to Python, builds `Solve`'s arguments with the
problem's own `Input.from_str`, and compares what it prints:

| Kind | Compared with |
|---|---|
| `strict` | the stored output |
| `loose` | what the original Python prints |

A row is strict when its original Python, run on the stored input text,
prints the stored output exactly. The rest are loose: they often have several
correct answers. A few strict rows are `unvalidatable`: the Python reads the
input text itself, but the harness must parse it with `Input.from_str`, and
`from_str` rejects their tests.

## Where the rows are

Each row is in exactly one of these (counts: `STATUS.md`):

| Directory | The row… |
|---|---|
| `solutions/` | passes its tests and `dafny verify`; the label audit found no problem |
| `solutions-unscreened/` | passes its tests; not yet label-audited or swept by `dafny verify` |
| `solutions-disputed/` | has a label or translation problem to review; not swept by `dafny verify` |
| `solutions-unsure/` | passes its tests and `dafny verify`; the label audit could not decide |
| `solutions-ungateable/` | cannot get a reliable test verdict |
| `solutions-unverified/` | passes its tests but fails `dafny verify` |
| `solutions-untranslated/` | prints a bare float, which Dafny cannot reproduce exactly |

`solutions-proved/` holds copies of rows with a machine-checked
complexity bound added; the rows themselves stay above.

Also here: `prelude.dfy` (shared helpers), `data/` (gate results and records),
`batches/` (campaign and audit records), `out/` (generated, git-ignored),
`COMPLEXITY.md` (the cost model), `STATUS.md` (all counts), `CHANGELOG.md`.

## Toolchain

Dafny 4.11.0, Z3 5.1.0, and Python 3 with `numpy` (`requirements.txt`; every
row's `Input` dataclass imports it). The scripts, grouped by job:

```bash
# dafny and z3 on PATH; numpy in a local venv. With the venv active,
# `python3` below is the venv's Python.
uv venv && uv pip install -r requirements.txt && source .venv/bin/activate
# build, in order (once, or when BigOBench changes)
python3 extract.py          # download BigOBench -> data/tasks.jsonl (git-ignored)
python3 signature.py        # dataclass -> Dafny Solve signatures -> data/signatures.jsonl
python3 scaffold.py         # .dfy stubs for untranslated rows; never overwrites a real body
python3 baseline.py         # original Python vs its own tests -> data/baseline.jsonl (--workers N)
python3 dataset.py          # join everything -> data/dataset.jsonl, data/stats.json
# gates: each answers one question (DOCS.md, "The gates")
python3 validate.py --self-test       # test validate.py itself (statuses: DOCS.md)
python3 validate.py                   # strict rows: stored output? (--only SID... for a spot check into out/)
python3 difftest.py --loose          # loose rows: same output as the Python?
python3 verify_all.py       # dafny verify every translation -> data/verification.jsonl
python3 precheck.py SID...    # every `requires` accepts every stored input? (--all)
python3 proofs.py           # every complexity proof verifies, no assume -> data/complexity_proofs.jsonl
# label audit
python3 label_audit.py evidence   # batches for an auditor -> out/labelaudit/
python3 label_audit.py check FILE # reject a malformed verdict file (apply runs it too)
python3 label_audit.py apply FILE # move rows by verdict -> data/label_audit.jsonl
python3 label_audit.py siblings   # same-problem rows whose labels differ
# reports
python3 prove_stats.py      # proof-campaign statistics -> data/prove_stats.md
python3 callgraph.py        # call depth per row -> out/call_depth.jsonl
python3 collect.py          # dashboard payload -> out/artifact_data.json (run callgraph.py first)
# libraries, never run directly: common.py (paths, IO), features.py (static
# facts from a .dfy), vocab.py (campaign record vocabularies)
```

