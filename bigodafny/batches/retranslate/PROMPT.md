FIRST ACTION: call the Skill tool with skill="my-concise". Follow it for all
prose. Code is exempt.

# Task
Each row in your manifest is a Dafny translation of a Python program. It passes
its tests and `dafny verify`, but an audit says the Dafny does NOT use the
Python's algorithm, so it has a different time complexity. Rewrite the Dafny so
it follows the Python's algorithm step for step, at the Python's complexity.

Working directory: bigodafny/ (from the repository root)
Manifest: batches/retranslate/w_{{NN}}.txt -- one row path per line. Edit each
file where it is; never move it. `dafny` and `z3` are on PATH. Python:
`.venv/bin/python3`.

For each row read, in this order:
1. The Python block in the file header (`// --- Python`).
2. The audit's finding: `grep '"sid": "<SID>"' data/label_audit.jsonl`, or the
   agent note below for rows with no `translation` verdict.
3. `COMPLEXITY.md` § The model: what each Dafny operation costs.

Agent notes for rows with no audit verdict (found during a verify pass):
- 1671_196: merge sort where the Python does insertion sort.
- 1742_66: linear scan where the Python sorts.
- 1853_137, 1853_66: O(n^2) pair loop where the Python sorts or counts.
- 565_158: counting array where the Python sorts.
- 700_233, 700_99: closed form where the Python loops k times.
- 1997_311: drops the Python's sort.

# What "the Python's algorithm" means
- Python `sorted`/`.sort` -> `Prelude.Sort`/`SortInts`/`SortStrings` (charged
  `SortCost(k)`), even when the output could be had without sorting.
- `dict`/`Counter`/`defaultdict` -> Dafny `map` (lookup, update: 1 step).
- `set` -> Dafny `set` (membership, insertion: 1 step).
- `heapq` -> a binary heap on a `seq<int>` with sift-up/sift-down,
  O(log n) per push/pop. Write it once per file.
- `bisect` -> a binary search loop.
- `sum(x[i:])` inside a loop -> a loop summing that slice each time
  (`SumSeq(x[i..])` is fine).
- Python insertion sort -> an insertion sort loop.
Keep every other part of the row as it is.

# When to change NOTHING
The model charges a slice `s[a..b]` 1 and a seq update 1, though Python copies.
So `a = a[1:]`, `del l[0]`, `s = s[:i] + s[i+1:]` in the Python are matched by
the Dafny's view or update; that is not a defect. If the Dafny already performs
the Python's steps and differs only in such charges, leave the row unchanged
and say "no change: <one-line reason>". Same if you conclude the audit is
wrong; give the reason.

# Gates after each row
1. `dafny verify <path> --verification-time-limit 30` -- must end
   `N verified, 0 errors` with no time-out. Add invariants as needed.
2. Strict rows: `.venv/bin/python3 validate.py --only <SID> --out-prefix rt{{NN}}_`
   Loose rows (validate.py says so, or the row is `loose` in
   `data/dataset.jsonl`): `.venv/bin/python3 difftest.py --only <SID>`
   (`agrees` passes). For loose rows reproduce the Python's choices exactly:
   which answer, which order, which index.
If a row will not pass both after ~12 tool calls, restore it with
`git checkout -- <path>` and report why.

# Rules
- **NEVER use `assume` or `decreases *`.**
- Keep the header, `include`, `import` and `Solve` signature verbatim. Keep
  every existing `requires`; add one only if the problem guarantees it (the
  parent checks each against every stored input).
- No `var` binding inside a `requires`.
- Never copy a body from a sibling row (same problem, other solution).
- Dafny has no floats; `/` and `%` are Euclidean (Python floors).
- Repeated `s := s + t` in a loop costs O(n^2): collect a `seq<string>`, `Join`
  once.
- Prelude (already imported; do not reimplement): FloorDiv FloorMod IntToString
  Join JoinInts SplitWs Sort SortInts SortStrings StringLess MaxSeq MinSeq
  SumSeq Gcd AbsInt Repeat ReplaceAll ParseInt ParseInts; lemmas
  `SortKeepsElems`, `SortIntsKeepsElems`, `SortIsPermutation`.

# Hard rules
- NEVER git add/commit/push/mv. `git checkout --` on your own files is allowed.
- Edit ONLY the files in your manifest. NEVER edit prelude.dfy, any *.py,
  anything under data/, batches/, or solutions-proved/.

# Report (concise)
- per row: `changed` (one line: what the Dafny now does), `no change` (reason),
  or `restored` (blocking error)
- every `requires` you added: row, clause
