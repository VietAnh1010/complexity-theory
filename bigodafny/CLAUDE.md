# bigodafny -- operating rules

**New here, or resuming with a clean context? Read `DOCS.md` first.** It is the
entry point: reading order, current state, the document map, and the one change
most likely to mislead you. Then `.claude/skills/bigodafny/SKILL.md` for the
map, gates and findings; sub-skills `bigodafny-translate`, `bigodafny-verify`,
`bigodafny-prove`. Then run `python3 dataset.py` and read `data/stats.json`;
the directory a row sits in is its status, never an earlier message.

Builds a Python -> Dafny translation dataset from BigOBench's
`time_complexity_test_set`. Independent of the arXiv paper-mining pipeline in
`../scripts`: no shared sources, cache, or record shape.

## Where a row lives

Six directories partition all 640 rows; each carries a `README.md` saying what
it means and how a row leaves it. A row is in exactly one.

| directory | rows | why it is not simply clean |
|---|---|---|
| `solutions/` | 342 | — it is |
| `solutions-unscreened/` | 127 | its label was never screened |
| `solutions-disputed/` | 159 | the audit says its label does not match its code |
| `solutions-ungateable/` | 5 | its gate cannot reach a verdict; the test data fails first |
| `solutions-unverified/` | 3 | `dafny verify` cannot discharge its safety obligations |
| `solutions-untranslated/` | 4 | it will not be translated; the file says why |

`solutions-proved/` is **not** part of that partition — it holds instrumented
copies (189 files over 187 rows: 2 tight-bound variants under `nlogn/`, 11
value-bounded rows queued for review under `value-bounded/`)
of rows that also live above. A row can exist in two places with different preconditions;
`precheck.py`'s `find_all` exists for that.

Older notes use the old names: `solutions-inexact/` → `solutions-unscreened/`,
`solutions-tofix/` → `solutions-disputed/`, `solutions-verified/` →
`solutions-proved/`, `solutions-nlogn/` → `solutions-proved/nlogn/`,
`solution-guessed-verified/` → `experiments/proofs-blind/`.

## The one rule that matters

**A row is valid only if the toolchain says so.** `dafny translate` must accept
it and every executed test must match. Never mark a translation valid because
it looks right, and never write an expected output by hand -- the expected
output is whatever BigOBench stored.

## No model is in this pipeline

`extract`, `signatures`, `scaffold`, `baseline`, `validate` and `dataset` are
deterministic. Re-running `extract` must produce a byte-identical
`tasks.jsonl`. If a translator is added later it writes into `solutions/` and
is judged by `validate` like anything else; it does not become part of these
stages.

## Rules

- **Measure, don't read the statement.** The `strict`/`loose` split comes from
  running the original Python, not from a regex over the description. The regex
  survives as `nondet_hint` and scores precision 0.38, recall 0.45 against the
  measurement -- that is why it does not gate anything.
- **Never claim a translation is correct beyond the tier you ran.** Default is
  public + private. `--generated` is a separate, larger claim.
- **Distinguish failure modes.** `build` (Dafny rejected it), `fail` (ran, wrong
  output), `timeout`, `error`. Collapsing them hides which half broke.
- **Never overwrite a real body.** `scaffold` skips any `.dfy` that exists.
  `--force` is for regenerating stubs and will discard translations.
- **Failures are data.** An unmappable signature is recorded with the offending
  annotation, never guessed and never silently dropped.
- **Run `selftest` after touching `validate.py`.** It asserts a wrong answer is
  reported as `fail` and a syntax error as `build`. It has already caught one
  bug where a fixture broke the `include` path and every case looked like a
  build failure.

## `solutions-untranslated/` is a decision, not a backlog

Four rows will not be translated. Each file states its own blocker in place of a
body, and carries no stub: there is nothing to fill in.

All four `print()` a bare Python float. Matching that byte-for-byte needs
bit-exact IEEE-754 arithmetic (Dafny's `real` is an exact rational and does not
round where a float rounds) **and** CPython's shortest-round-trip repr. Both
gates compare stdout as text, so both are inapplicable rather than failing.

The same problem with a format spec is tractable: `solutions/2496/2496_30.dfy`
computes in exact rationals and replicates `'{:.9}'.format(x)`, agreeing on all
42 comparable tests. It is bare `print(float)` that has no finite specification.

`scaffold.py` treats these as present, so re-running never regenerates a stub.

## Two gates, and which row gets which

`validate.py` compares a translation's stdout against BigOBench's **stored**
output. That is the right question for the 534 `strict` rows.

It is the wrong question for the 100 `loose` rows. Their problems accept more
than one correct answer -- Codeforces judged them with token-based or special
checkers -- so the stored output is one accepted answer among several, and even
the original Python fails a byte-diff against it. Scoring those rows with
`validate.py` measures the checker, not the translation.

`difftest.py` is their gate: run the row's own Python and its Dafny on the same
inputs, compare the two outputs to **each other**. Status `agrees` is a pass.
That is the real question for a transpilation dataset, and it stays decidable
where the stored output does not.

Consequence for how loose rows are translated: **be literal**. Where the Python
picks arbitrarily among valid answers -- which one, what order, which index --
reproduce that exact choice. A tidier answer is a failure. Reproduce bugs too.

## A gate result can be wrong without the gate being wrong

`validate.py` marshals a test's input through the problem's own
`Input.from_str` before handing the fields to the Dafny. When it reports `fail`,
three things could be at fault: the translation, the stored test, or the
dataclass between them. The gate only ever runs one implementation, so it
cannot tell them apart.

`batches/gate-audit/control.py` is the missing control: it runs the **original
Python** through the same round-trip. A test the round-trip cannot parse, or
one the Python then fails, is evidence about the harness, not the translation.

Five rows turned out that way and now live in `solutions-ungateable/`, with
`data/gate_ungateable.jsonl` as the record and a `GATE INAPPLICABLE` header in
each file.

`dataset.py`'s `parser_ok` already marked four of them **`unvalidatable`** —
it runs `from_str` over every stored test and fails a row when it raises or
when a `real` argument does not survive the float round-trip. Read that split
before concluding a row has "no gate result"; a tool that reads
`validation.jsonl` directly will report the absence as if it were a finding.

**Neither gate was touched.** A gate relaxed until the rows pass has stopped
measuring anything, so the rows moved instead: `solutions/` keeps
meaning "the gate says yes", and a row whose gate can say nothing is filed as
exactly that.

**Neither gate may be edited by an agent whose work it judges.** An agent
lowered difftest's per-test budget for the reference Python from 30s to 10s
while fixing a real `sys.stdin.buffer` defect in the same edit. The fix was
kept; the budget cut was reverted. Slow rows would have been marked
`python-failed` and dropped out of the comparison, so the gate would have passed
more rows by checking fewer.

## Value counts as a parameter

**Decided 2026-09-17.** A loop bounded by an input *value* is not constant. The
value enters the bound as its own parameter — `O(log v)` for a binary search
over `v`, `O(r)` for `while i < r`, `O(L)` for a per-character comparison.

Treating a capped value as `O(1)` is formally defensible and practically
useless: the hidden constant is then 30 to 60, and a label with a constant that
size predicts nothing about growth. `COMPLEXITY.md` § 1 is the authority.

BigOBench fitted its labels by profiling, which assumes the opposite, so the two
disagree wherever a value-bounded loop appears. Five rows have moved to
`solutions-disputed/` on that basis: four on 2026-09-17, recorded in
`batches/prove-sample/value_vs_size_decision.jsonl` with the two rows the
decision unblocked, and `276_610` on 2026-09-22, found by `prove-sample-4`.

**The convention settled how to count a value; it did not make the proofs
easy.** Connecting a value-bounded cost back to a bound in the row's size is
the single most common reason a proof fails: 4 of 11 in `prove-sample-3` and
5 of 12 in `prove-sample-4`, coded `value-to-size`. Each needs its own
arithmetic lemma (`Pow10Mono`, a doubling-search invariant, a triangular-number
bound, a sortedness fact the prelude does not have), and none of it carries to
the next row.

> **Corrected 2026-09-21.** After campaign 3 this file claimed the label had
> stopped predicting difficulty, `O(nlogn)` climbing 5/11 → 7/11 → 10/12 while
> `O(n)` fell 24/24 → 20/23 → 12/18. **Campaign 4 did not reproduce it**:
> `O(n)` came back at 21/25 and `O(nlogn)` at 7/10. Pooled over four campaigns
> `O(n)` is 77/90 = 86% and `O(nlogn)` is 29/44 = 66% — campaign 1's ordering,
> less extreme than it looked. Campaign 3's `O(n)` cell tests at p = 0.036
> against the pooled rate, which does not survive the eight comparisons the
> table invites. A class holds 8 to 25 rows per campaign, so two rows move the
> rate ten points. `collect.py`'s `campaign_series` now reports the pooled rate
> and a per-cell binomial test; read that, not one campaign's column.

What does survive is the obstacle, not the rate. `value-to-size` was named
independently by campaign 4's agents, none of which had seen campaign 3.

### Where these rows go

`solutions-proved/value-bounded/` collects them, 18 so far. It is an **overlay
subdirectory** like `nlogn/`, not a partition member: the row stays wherever
the partition puts it, and `MANIFEST.jsonl` records its `row` path.

File a row there whenever a campaign produces either:

Two destinations, by whether a proof exists. A row with no proof does **not**
go under a directory called `solutions-proved`:

| from | condition | where it goes |
|---|---|---|
| `label_relation.jsonl` | `relation: looser-structural` **and** the reason names an input value | `git mv` its proof from `solutions-proved/<pid>/` into `solutions-proved/value-bounded/<pid>/`, fix the `include` to `../../../prelude.dfy`, add the `VALUE-BOUNDED` header, append to that directory's `MANIFEST.jsonl` |
| `obstacles.jsonl` | `obstacle: value-to-size` | no proof exists — append to `batches/value-bounded-open/MANIFEST.jsonl`, no file to move |

Name the campaign that found it either way. Nothing leaves either directory
except by a reviewer's decision; the three exits are in their READMEs. Do not
relax the convention for one row.

**`prelude.dfy` gained `SortIsSorted` and `SortLastIsMax` on 2026-09-22.**
Until then `Sort` proved only `SortIsPermutation` — its output is a
rearrangement of its input — and nothing said the output was ordered, so no
proof could say "the last element is the maximum". `2423_48` failed on exactly
that: its trip count is `d[|d|-1].0 + 2`, which could not even be named. The
lemmas require `StrictTotalOrder(less)`; `IntLessIsTotalOrder` discharges that
once for `int`, and `SortIntsIsSorted` is the ready-made corollary. `2423_48`
has not been retried.

## The cost model is stipulated, not measured

`COMPLEXITY.md` § 1 is the authority. `s[i := v]`, `m[k := v]`, `s + [x]`,
`s[a..b]` and set insertion are each charged **1**, as an axiom, independent of
any backend. Do not charge a collection operation what Dafny's Python backend
costs; the labels were measured on CPython, so a backend-derived model compares
two unrelated implementations.

This is a change, and it invalidates older notes. `set<T>` built in a loop is
O(n**2) in the Python backend -- measured, 0.017 / 0.070 / 0.278s as n doubles
from 2000, against 0.004 / 0.006 / 0.011s for a `seq` -- and that used to make
a row disagree with its own label. It no longer does. The measurement lives in
`COMPLEXITY.md`'s appendix as a performance note, which is what it always was.

The two places the divergence still decides something: `solutions/2826_42` and
`solutions/2128_34` keep an `array<T>` because their tables are too large for
the backend to copy per update. They are the corpus's only arrays, and each
says so in a header comment.

Same shape as the doubly-recursive min/max trap: correct output, wrong
complexity, green tests.

## Translate the algorithm, not just the behaviour

**The validator cannot catch this one.** It checks stdout against stored tests.
A translation that computes the right answer by a different algorithm passes
every test and still corrupts the dataset.

Every row carries BigOBench's time complexity label, measured on *that* Python.
Two rows of the same problem exist precisely because they differ: problem 1861
has `1861_16` at O(n) and `1861_28` at O(n**2). A wave-5 agent reimplemented
`1861_28` using `1861_16`'s DP. All tests passed. The row then claimed O(n**2)
while running O(h*w) -- the label, which is the dataset's whole point, became a
lie. Reverted.

So: match the source's asymptotic shape. Restructuring within a complexity class
is fine and often necessary -- a `seq<T>` buffer filled by index instead of
O(n**2) string concatenation, an exact rational instead of a float, a
mod-reduced product instead of a literal factorial. Replacing the algorithm is
not.

When two solutions of one problem look like they want the same code, that is the
signal to check their labels, not to share an implementation.

## `assume {:axiom}` in translations

Some translations carry `assume {:axiom} ...` to discharge static bound proofs
that follow from problem constraints but not from local loop structure.

This is sound for THIS dataset and unsound for a different one. The gate here is
`dafny translate --no-verify` plus the stored tests, and `assume` is erased at
compile time -- verified: the emitted Python contains zero occurrences. So it
cannot affect the behaviour the tests measure.

But anyone who later runs `dafny verify` over `solutions/` will get vacuous
successes wherever an `assume` sits. If verification ever becomes the gate,
every `assume` must be discharged or removed first. Count them before trusting
a verification result:

    grep -rho "assume\s*{:axiom}" solutions --include='*.dfy' | wc -l

## Toolchain

Dafny **4.11.0** (`dotnet tool install -g dafny --version 4.11.0`), Z3 4.12.1
(`pip install z3-solver==4.12.1.0`), numpy (every `dataclass_code` imports it at
module scope). The Dafny version is part of the reproducibility contract and is
recorded in `stats.json`.

## Gotchas that cost real time

- Dafny `/` and `%` are **Euclidean**; Python `//` and `%` **floor**. They agree
  only when the divisor is positive. Use `Prelude.FloorDiv`/`FloorMod`.
- `dafny translate py` needs `--include-runtime`, or `_dafny` is missing.
- A Dafny `string` returns as `_dafny.Seq`; call `.VerbatimString(False)`.
- `seq<int>` accepts a bare Python list, but `string` and nested types do not --
  `validate.conv_expr` builds the marshaller per type.
- Parameters named `string`, `map`, `set` are legal Python and illegal Dafny.
  `signature.safe_name` renames them.

## Style

The `my-concise` skill governs anything said to the user and `STATUS.md`:
bullets, one claim each, ~100 characters, no hedges. It ships with the
environment now, not with this repo.
