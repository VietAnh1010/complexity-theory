---
name: bigodafny-translate
description: Spawn agents to translate BigOBench Python solutions into Dafny in bigodafny/. Use when rows still carry a "TODO: translate" stub, or when asked to translate, port, or finish porting examples to Dafny. Produces the agent prompt and the audit procedure.
---

# Translating rows to Dafny

Read the `bigodafny` skill first for directory meanings and gates.

## Pick the work

```bash
cd bigodafny
grep -rl 'TODO: translate' solutions --include='*.dfy' | sed 's|.*/||; s|\.dfy||' | sort
python3 -c "
import json
ds={r['solution_id']:r for r in (json.loads(l) for l in open('data/dataset.jsonl'))}
# split decides the gate: strict -> validate.py, loose -> difftest.py"
```

Manifests of ~20 ids under `batches/<name>/`, 4 agents at a time.

## Agent prompt

Give each agent: its manifest path, a unique validation prefix, and this body.

    FIRST ACTION: call the Skill tool with skill="my-concise".

    Working directory: /home/user/complexity-theory/bigodafny
    Start every Bash call that invokes dafny with:
        export PATH="$PATH:/root/.dotnet/tools"

    CONTRACT
    method Solve(<args>) returns (output: string) returns the ENTIRE stdout the
    Python would print. Arguments arrive already parsed -- do NOT parse stdin in
    Dafny. Replace ONLY the stub body; keep header, include, import and
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
        dafny verify solutions/<PID>/<SID>.dfy --solver-path /usr/local/bin/z3 \
            --verification-time-limit 30
    - while i < |a| invariant 0 <= i <= |a| decreases |a| - i
    - `invariant i <= n` with an unconstrained int n FAILS on entry; drop the
      upper bound, or `requires n >= 0` only if the problem guarantees it
    - invariant |buf| == i   (Dafny forgets a seq's length across a loop)
    - forall k :: 0 <= k < |xs| ==> |xs[k]| >= 2   (nested input shape)
    NEVER `assume`. Unverified beats a hollow proof. Every `requires` is checked
    by the parent against all stored inputs and reverted if it fails.

    PRELUDE (already `import opened`; do not reimplement)
        FloorDiv FloorMod IntToString Join JoinInts SplitWs
        Sort SortInts SortStrings StringLess   (all carry length `ensures`)
        MaxSeq MinSeq SumSeq Gcd AbsInt Repeat ReplaceAll
        ParseInt ParseIntFrom ParseInts BitOr BitAnd BitXor

    TRAPS
    - Sort over tuples needs explicit lambda parameter types
    - `if MaxOf(xs[1..]) > xs[0] then MaxOf(xs[1..]) else xs[0]` recurses twice
      -> EXPONENTIAL, passes small tests. Use MaxSeq/MinSeq or bind the result
    - set<T> built in a loop is O(n**2) in Dafny's Python backend (measured)
    - Dafny has no floats; use exact integer or rational arithmetic
    - `/` and `%` are EUCLIDEAN; Python floors. Same only when divisor > 0
    - repeated `s := s + t` in a loop is O(n^2): accumulate seq<string>, Join once
    - the generated Input fields do NOT always equal what the Python reads.
      If outputs are off by a constant, read .build/<PREFIX>_<SID>/dataclass.py

    SURVIVE INTERRUPTION -- the session limit kills agents mid-batch.
    Write EACH translation DIRECTLY to its .dfy, never a temp name. Validate in
    groups of ~5 as you go; unvalidated work is discarded. ~8 tool calls per row,
    then restore `  output := ""; // TODO: translate the Python above`.

    HARD RULES
    NEVER git add/commit/push. NEVER edit prelude.dfy, any *.py, or anything
    under data/, batches/, summaries/. Only files in your manifest.

    REPORT: valid count; how many also verify; rows given up with one line each;
    sibling pairs and how their algorithms differ.

## Audit before committing

Never trust the agent's count.

```bash
python3 validate.py --only $(cat batches/<b>.txt | tr '\n' ' ') --out-prefix audit_
python3 difftest.py --only <loose ids>
for sid in $(cat batches/<b>.txt); do pid="${sid%%_*}"
  dafny verify solutions/$pid/$sid.dfy --solver-path /usr/local/bin/z3 \
    --verification-time-limit 30 | grep -q "0 errors" || echo "unverified: $sid"; done
python3 precheck.py $(cat batches/<b>.txt | tr '\n' ' ')
grep -rl assume solutions --include='*.dfy' | wc -l     # must stay 0
```

A row that fails is reverted to its stub, not committed. Then re-discriminate
(see the `bigodafny` skill) and commit.
