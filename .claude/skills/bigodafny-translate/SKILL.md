---
name: bigodafny-translate
description: Spawn agents to translate BigOBench Python solutions into Dafny in bigodafny/. Use when a row's Dafny does other work than its Python (STATUS.md § Known issues), or when asked to translate, re-translate or port examples to Dafny. Produces the agent prompt and the audit procedure.
---

# Translating rows to Dafny

Read the `bigodafny` skill first for directory meanings and gates.

## Pick the work

Every translatable row has a body. The work is re-translating rows whose Dafny does other work
than its Python: `STATUS.md` § Known issues lists them, and each `prove-disputed-*/README.md` says
how they differ. A row's `split` in `data/dataset.jsonl` decides its gate: `strict` ->
`validate.py`, `loose` -> `difftest.py`. Rows stay where they are (often `solutions-disputed/`).

Manifests of ~20 ids under `batches/<name>/`, 4 agents at a time.

## Agent prompt

Give each agent: its manifest path, a unique validation prefix, and this body.

    FIRST ACTION: call the Skill tool with skill="my-concise".

    Working directory: bigodafny/ (from the repository root)
    `dafny` and `z3` are on PATH.

    CONTRACT
    method Solve(<args>) returns (output: string) returns the ENTIRE stdout the
    Python would print. Arguments arrive already parsed -- do NOT parse stdin in
    Dafny. Rewrite ONLY the method bodies and helpers; keep header, include, import and
    signature verbatim.

    GATE
    strict rows:  python3 validate.py --only SID... --out-prefix <PREFIX>_
    loose rows:   python3 difftest.py --only SID...        ("agrees" passes)
    difftest compares your Dafny against the row's OWN Python, because these
    problems accept several correct answers and the stored output is only one.

    For loose rows: BE LITERAL. Reproduce the Python's arbitrary choices --
    which valid answer, what order, which index -- and reproduce its bugs. A
    tidier answer is a failure.

    RULE ZERO -- never reuse a translation between two solutions of one problem.
    Siblings are in the dataset BECAUSE their measured complexity labels differ.
    Translate each from its own Python. An earlier agent copied one sibling's
    body to another; every test passed and the row still claimed O(n**2) while
    running an O(n) DP.

    ALSO MAKE IT VERIFY (~3 extra calls per row)
        dafny verify <the row's path> \
            --verification-time-limit 30
    - while i < |a| invariant 0 <= i <= |a| decreases |a| - i
    - `invariant i <= n` with an unconstrained int n FAILS on entry; drop the
      upper bound, or `requires n >= 0` only if the problem guarantees it
    - invariant |buf| == i   (Dafny forgets a seq's length across a loop)
    - forall k :: 0 <= k < |xs| ==> |xs[k]| >= 2   (nested input shape)
    NEVER `assume`. Unverified beats a hollow proof. Every `requires` is checked
    by the parent against all stored inputs and reverted if it fails. No `var`
    binding inside a `requires`.

    PRELUDE (already `import opened`; do not reimplement)
        FloorDiv FloorMod IntToString Join JoinInts SplitWs
        Sort SortInts SortStrings StringLess   (all carry length `ensures`)
        MaxSeq MinSeq SumSeq Gcd ISqrt AbsInt Repeat ReplaceAll
        ParseInt ParseIntFrom ParseInts BitOr BitAnd BitXor

    KEEP THE PYTHON'S ALGORITHM (the label belongs to it)
    - sorted/.sort -> Sort/SortInts/SortStrings, even when the output could be
      had without sorting
    - dict/Counter/defaultdict -> map; set -> set
    - heapq -> a binary heap on a seq<int> with sift-up/sift-down, written once
      per file
    - bisect -> a binary search loop
    - sum(x[i:]) inside a loop -> sum that slice each time (SumSeq(x[i..]))
    - a square root -> ONE ISqrt call where the Python takes it:
        math.isqrt(x), int(math.sqrt(x)), int(x ** 0.5) -> ISqrt(x)
        math.ceil(math.sqrt(x)) -> var r := ISqrt(x); if r * r < x { r := r + 1; }
        perfect-square test -> var r := ISqrt(x); r * r == x
        range(..., int(sqrt(n)) + 1) -> compute ISqrt(n) once, loop to it
      never a search loop of your own; keep a Python loop `while i * i <= n`

    TRAPS
    - Sort over tuples needs explicit lambda parameter types
    - `if MaxOf(xs[1..]) > xs[0] then MaxOf(xs[1..]) else xs[0]` recurses twice
      -> EXPONENTIAL, passes small tests. Use MaxSeq/MinSeq or bind the result
    - set/map/seq updates are charged O(1) (COMPLEXITY.md axioms), though the
      Python backend copies. Slow to RUN, not a label defect. Do not use array<T>
    - Dafny has no floats; use exact integer or rational arithmetic
    - `/` and `%` are EUCLIDEAN; Python floors. Same only when divisor > 0
    - repeated `s := s + t` in a loop is O(n^2): accumulate seq<string>, Join once
    - the generated Input fields do NOT always equal what the Python reads.
      If outputs are off by a constant, read .build/<PREFIX>_<SID>/dataclass.py

    SURVIVE INTERRUPTION -- the session limit kills agents mid-batch.
    Write EACH translation DIRECTLY to its .dfy, never a temp name. Validate in
    groups of ~5 as you go; unvalidated work is discarded. ~8 tool calls per row,
    then restore the row with `git checkout -- <path>`.

    HARD RULES
    NEVER git add/commit/push. NEVER edit prelude.dfy, any *.py, or anything
    under data/ or batches/. Only files in your manifest.

    REPORT: valid count; how many also verify; rows given up with one line each;
    sibling pairs and how their algorithms differ.

## Audit before committing

Never trust the agent's count.

```bash
python3 validate.py --only $(cat batches/<b>.txt | tr '\n' ' ') --out-prefix audit_
python3 difftest.py --only <loose ids>
for sid in $(cat batches/<b>.txt); do pid="${sid%%_*}"
  f=$(ls solutions{,-*}/$pid/$sid.dfy | grep -v solutions-proved)
  dafny verify "$f" \
    --verification-time-limit 30 | grep -q "0 errors" || echo "unverified: $sid"; done
python3 precheck.py $(cat batches/<b>.txt | tr '\n' ' ')
grep -rl assume solutions* --include='*.dfy' | wc -l    # must stay 0
```

A row that fails is reverted (`git checkout -- <path>`), not committed. A changed row with a proof in
`solutions-proved/` needs a new proof: `proofs.py` flags the old one (`same_python: differs`).
Then commit.
