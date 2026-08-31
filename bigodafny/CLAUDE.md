# bigodafny -- operating rules

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
