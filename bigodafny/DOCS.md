# Working on BigODafny

Everything for BigODafny is in this directory. The paper-mining project at the
repository root is unrelated.

## Start here

| To… | Read |
|---|---|
| understand the dataset and its directories | `README.md` |
| change a translation or move a row | `CLAUDE.md`, then each affected directory's `README.md` |
| review a label | `COMPLEXITY.md`, `solutions-disputed/README.md`, `batches/labelaudit/PROMPT.md` |
| write a proof | `COMPLEXITY.md`, `solutions-proved/README.md`, `batches/CAMPAIGN_CONFIG.md` |
| see counts and results | `STATUS.md`; campaigns: `data/prove_stats.md` |
| see what changed | `CHANGELOG.md` |

`summaries/` and old campaign prompts are history, not instructions.

## Terms defined by this project

Standard terms (ghost code, `decreases *`, test harness) are used in their
usual sense. These have a meaning specific to this project:

| Term | Meaning |
|---|---|
| row | one Python solution and its Dafny translation. Its id (`solution_id`) starts with its problem's id: `1950_45` is a solution to problem `1950` |
| label | BigOBench's time complexity for the row's Python, one of eleven classes: `O(1)`, `O(logn)`, `O(n)`, `O(nlogn)`, `O(n**2)`, `O(n*m)`, `O(n+m)`, `O(n+mlogm)`, `O(nlogn+mlogm)`, `O(n+m)log(n+m)`, `O(n**2+m**2)` |
| strict / loose (tier) | a strict row is tested against its stored output; a loose row against what its original Python prints (`README.md`) |
| unvalidatable | a strict row whose tests the problem's own `Input.from_str` rejects, so `validate.py` cannot run them |
| status directory | one of the seven `solutions*` directories a row sits in; `solutions-proved/` is not one |
| gate | a script that decides whether a row passes a check; a failed gate keeps the row out of `solutions/` |
| verified / proved | verified: `dafny verify` accepts the row (safety). Proved: a copy in `solutions-proved/` has a checked complexity bound |
| label audit | an AI auditor reads a row and returns a verdict on its label: `ok`, `mismatch` or `unsure`, with the class it thinks is right (`true_class`) |
| round (r1–r4) | one pass of the label audit under the rules of its day (`batches/README.md`) |
| main agent | the Claude session that runs an audit or campaign and reviews its agents' output |
| override | a verdict the main agent replaced after review; its `auditor` field starts with `main agent` |
| file header | a comment block at the top of a row's file recording a review: `LABEL AUDIT`, `TRANSLATION AUDIT`, `GATE INAPPLICABLE`, `VALUE-BOUNDED` |
| sibling | another solution to the same problem. Sibling convergence: two siblings with different labels whose Dafny is nearly identical |
| quarantine | setting a row aside for review without removing it from the dataset (`data/quarantine.jsonl`) |
| naming rule | a label names every size it depends on (`COMPLEXITY.md`) |
| value-bounded | a row whose cost depends on how large an input value is, not only on how many inputs there are (`solutions-proved/value-bounded/`) |
| campaign | a batch run in which agents try to prove rows' labels under a fixed time and attempt budget |
| draw / fresh row | the rows a campaign picks to attempt; a fresh row is one no earlier campaign drew |
| obstacle | the coded reason a campaign row stayed unproved |
| relation | how a proved bound compares with the label, e.g. `confirms` (`COMPLEXITY.md` § Proof relations) |
| `audit.py` | the campaign checker, in `.claude/skills/bigodafny-prove-campaign/scripts/` |

## Counts

All counts are in `STATUS.md`.

A row's directory is its current state; don't infer it from old records.
Label verdicts are in `data/label_audit.jsonl`. A row with a failing gate stays
out of `solutions/` whatever its label verdict.

## The gates

A gate decides whether a row passes one check. A row stays in `solutions/` only
if it passes its test gate (`validate.py`, or `difftest.py` for a loose row)
and `dafny verify` (`verify_all.py`). A row that passes its tests but fails
`dafny verify` goes to `solutions-unverified/`. Passing one gate says nothing
about the others.

| Gate | Question | Runs on |
|---|---|---|
| `validate.py` | Does a strict row print the stored output? | every status directory except `solutions-ungateable/` and `solutions-untranslated/` |
| `difftest.py --loose` | Does a loose row print what the original Python prints? | every status directory except `solutions-ungateable/` and `solutions-untranslated/` (`--only` reaches any row) |
| `verify_all.py` | Does `dafny verify` pass (indexes in range, no division by zero, loops and recursion end)? | `solutions/`, `solutions-unsure/`, `solutions-ungateable/` (`--unscreened` adds that directory) |
| `precheck.py SID...` | Does every `requires` accept the row's real inputs? Dafny compiles and evaluates each clause | the rows named; `--all` every row with one |
| `proofs.py` | Does each complexity proof verify, without `assume`? | `solutions-proved/` and `prelude.dfy` |

`validate.py` statuses: `valid`, `fail` (wrong output), `build` (Dafny would
not compile), `timeout`, `error`.

The test gates and `baseline.py` skip tests outside a limit the problem
statement sets, listed with the quoted statement in `data/constraints.jsonl`,
and record how many as `tests_out_of_spec` (`out_of_spec` in `precheck.py`).
A problem with no entry counts every test.

Other checks, which move no rows:

| Script | Question |
|---|---|
| `label_audit.py check` | Is a verdict file well formed? |
| `label_audit.py siblings` | Did two siblings converge despite different labels? |
| `baseline.py --round-trip` | Is a failing strict row the harness's fault? |

## Rules

`CLAUDE.md`. Records follow the rules of their day; `CHANGELOG.md` dates every
rule change, so check it before reusing an old record.

## Proof campaigns

`batches/prove-sample*`: what each campaign drew (manifest), every attempt
(`traj_*.jsonl`, with an `obstacle` code when unresolved), and each proof's
relation to its label (`label_relation.jsonl`). Settings changed between
campaigns; read `batches/CAMPAIGN_CONFIG.md` before combining numbers.
