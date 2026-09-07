# bigodafny -- operating rules

**Resuming with a clean context?** Read `.claude/skills/bigodafny/SKILL.md`
first -- it holds the map, the gates, and the findings. Sub-skills:
`bigodafny-translate`, `bigodafny-verify`, `bigodafny-prove`. Then run
`python3 dataset.py` and read `data/stats.json`; the directory a row sits in is
its status, never an earlier message.

Builds a Python -> Dafny translation dataset from BigOBench's
`time_complexity_test_set`. Independent of the arXiv paper-mining pipeline in
`../scripts`: no shared sources, cache, or record shape.

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

**Neither gate may be edited by an agent whose work it judges.** An agent
lowered difftest's per-test budget for the reference Python from 30s to 10s
while fixing a real `sys.stdin.buffer` defect in the same edit. The fix was
kept; the budget cut was reverted. Slow rows would have been marked
`python-failed` and dropped out of the comparison, so the gate would have passed
more rows by checking fewer.

## `set<T>` is O(n**2) to build in the Python backend

Measured, not assumed. Doubling n quadruples the time:

    n=2000  0.017s     n=4000  0.070s (4.1x)     n=8000  0.278s (4.0x)

against a `seq` built the same way at 0.004 / 0.006 / 0.011s. Dafny's Python
runtime backs `set<T>` with a frozenset and does an incremental union per
insert, copying each time.

This matters more here than a normal performance note would. Every row carries a
complexity label, so a translation that builds a set inside a loop silently
carries an extra factor of n and stops matching its own label -- and the tests
still pass, because they are small. Use a sorted `seq` with binary search for
large lookup structures.

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
is fine and often necessary -- an array-backed buffer instead of O(n**2) string
concatenation, an exact rational instead of a float, a mod-reduced product
instead of a literal factorial. Replacing the algorithm is not.

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

`../.claude/skills/my-concise/SKILL.md` governs anything said to the user and
`STATUS.md`: bullets, one claim each, ~100 characters, no hedges.
