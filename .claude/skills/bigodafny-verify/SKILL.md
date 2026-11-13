---
name: bigodafny-verify
description: Discharge Dafny safety obligations on bigodafny/ translations that already pass their tests. Use when rows sit in solutions-unverified/, when `dafny verify` reports index-out-of-range or decreases errors, or when asked to run a verification pass or move rows out of solutions-unverified/.
---

# Making a translation verify

Read the `bigodafny` skill first for directory meanings and gates.

This is a **separate pass from translation**. The row already reproduces the
Python. Nothing it computes may change. What is missing is the proof that it is
memory-safe and terminates.

## What is actually being proved

No pre/postcondition is needed for `dafny verify` to have work to do. Every
`s[i]` carries `0 <= i < |s|`, every `/` and `%` carries a non-zero divisor, and
every loop carries a `decreases` that must decrease. A row that fails is not a
failing test — it passes every stored test. It means the translation faults on
some input the tests do not contain. Python raised `IndexError` where Dafny's
compiled code has undefined behaviour, so the original was never under this
obligation.

## Pick the work

```bash
cd bigodafny
mkdir -p batches/verifyN
find solutions-unverified -name '*.dfy' | sed 's|.*/||; s|\.dfy||' | sort \
  | split -l 20 -d -a 2 --additional-suffix=.txt - batches/verifyN/w_
```

~20 rows per agent, 4 agents at a time. Give each a unique validation prefix.

## Agent prompt

    FIRST ACTION: call the Skill tool with skill="my-concise". Follow it for all
    prose. Code is exempt.

    # Task
    Make 20 existing Dafny translations pass `dafny verify`. They already pass
    their tests. Do NOT change what they compute.

    Working directory: bigodafny/ (from the repository root)
    Manifest: batches/<name>/w_NN.txt   Files: solutions-unverified/<PID>/<SID>.dfy
    `dafny` and `z3` are on PATH.

        dafny verify solutions-unverified/<PID>/<SID>.dfy --verification-time-limit 30

    # What you are fixing
    Dafny raises obligations with no specification written: every `s[i]` needs
    `0 <= i < |s|`, every `/` needs a non-zero divisor, every loop needs a
    `decreases` that decreases. These rows were written before verification was
    a goal.

    # The fixes that worked
    1. **`invariant i <= n` where `n` is an unconstrained `int` parameter fails
       on entry** -- Dafny cannot assume `n >= 0`. Drop the upper bound, or add
       `requires n >= 0` if the problem guarantees it. Most common blocker.
    2. `while i < |a| invariant 0 <= i <= |a| decreases |a| - i`
    3. A loop setting a break flag without advancing its counter fails
       `decreases`. Force the counter to its terminal value on the break path,
       or use lexicographic `decreases !flag, bound`.
    4. Dafny forgets a seq's length across a loop: `invariant |buf| == i`.
    5. Nested/ragged shape: `forall k :: 0 <= k < |xs| ==> |xs[k]| >= 2`.
    6. Carry a searched index forward: `invariant idx == -1 || 0 <= idx < p`.
    7. `Prelude.FloorDiv(a, b)` requires `b != 0`; establish it.
    8. `Prelude.Sort`/`SortInts`/`SortStrings` carry `ensures |Sort(s,less)|
       == |s|`, and the prelude lemmas `SortKeepsElems`, `SortIntsKeepsElems`,
       `SortStringsKeepsElems`, `SortIsPermutation` give you the contents back
       across a sort. Call the lemma; do not hand-roll one. State the fact you
       need in MEMBERSHIP form (`forall x :: x in arr ==> P(x)`), not indexed
       form -- that is what the lemma delivers.
    9. `Prelude.MaxSeq`/`MinSeq` require `|s| > 0` and have NO membership
       postcondition. If you need `MaxSeq(s) in s`, prove it locally by
       induction on `MaxSeqFrom`.
    10. A verifier time-out: add `{:isolate_assertions}` to the method, or split
        a long method's facts into small lemmas.
    11. Python wraps a negative subscript; Dafny faults. If the Python reads
        `a[-1]`-style indexes, the fix is `Prelude.PyIndex`, not a `requires`.

    # Rules, in priority order
    - **NEVER use `assume`, in any form.** `assume {:axiom} 0 <= idx < |a|`
      verifies silently and discharges nothing. A row left unverified is
      strictly better.
    - **NEVER use `decreases *`.** Write a real `decreases` clause.
    - **Prefer an invariant to a precondition.** An invariant proves the code
      safe; a precondition narrows the contract until it is.
    - Any `requires` you add must be something the PROBLEM guarantees -- read
      the Python and description in the file header. The parent checks every
      added precondition against every stored test input and reverts ones that
      fail.
    - No `var` binding inside a `requires`: state it over the parameters.
    - Do not change the algorithm, the signature, or any computed value.

    # Loop
    1. Verify, read the error, add the invariant, re-verify.
    2. ~8 tool calls per row. If it will not verify, LEAVE IT AS IT WAS and
       report a one-line diagnosis. Unverified is an acceptable outcome.
    3. After every ~5 rows changed, confirm behaviour is unchanged:
           python3 validate.py --only SID1 SID2 ... --out-prefix vaA_
       Some rows are `loose` and validate.py cannot score them -- for those use
           python3 difftest.py --only SID1 SID2 ...
       (`agrees` is the pass). If a row regresses, revert it with
       `git checkout -- solutions-unverified/<PID>/<SID>.dfy`.

    # Hard rules
    - NEVER git add/commit/push. `git checkout --` on your own 20 files is
      allowed.
    - NEVER edit prelude.dfy, any *.py, or anything under data/, batches/,
      or any solutions*/ directory other than solutions-unverified/.

    # Report (concise)
    - how many of 20 now verify
    - how many needed an added `requires`, and what each says
    - rows you could not fix, one line each

## Audit before committing

Three things can go wrong and only one of them shows in the agent's report.

```bash
cd bigodafny
B=batches/verifyN/w_01.txt

# 1. re-verify from scratch -- never trust the count
for sid in $(cat $B); do pid="${sid%%_*}"; f=$(ls solutions*/$pid/$sid.dfy)
  dafny verify "$f" --verification-time-limit 30 \
    2>&1 | grep -q "0 errors" || echo "still unverified: $sid"; done

# 2. no hollow proofs
grep -rn 'assume' solutions-unverified --include='*.dfy'      # must be empty
grep -rn 'decreases \*' solutions-unverified --include='*.dfy'  # must be empty

# 3. every added requires holds on real inputs
python3 precheck.py $(cat $B | tr '\n' ' ')

# 4. behaviour unchanged
python3 validate.py --only $(cat $B | tr '\n' ' ') --out-prefix audit_
python3 difftest.py --only <the loose ids among them>
```

`precheck.py` compiles each `requires` with Dafny, as its own method, and runs
it on every stored input: any clause Dafny can compile is checked.

**The rule.** A precondition must not exclude an input the original Python
*answers*. Excluding an input the Python itself *crashes on* is fine — the row's
contract is to reproduce that Python, and there is nothing there to reproduce.
precheck measures this: it runs the row's own `solution_code` on every violating
input and reports `py-fails` separately from `VIOLATED`.

So an `exists` precondition is fine when the Python raises without it —
`p.index(k)` raising ValueError, `m // 0` raising ZeroDivisionError.

**Read its five counters, not just VIOLATED.** `unchecked` means the shape did
not translate; `no-data` means it translated and then raised on every input.
Both are "not checked", and neither is a pass. `py-fails` is a pass, with the
exemption above.

**A precondition is how a verification pass fakes itself.** Narrow the contract
far enough and the obligation is trivial. That is why step 3 is not optional and
why the agent is told the parent will run it.

Then move each verified row with `git mv`: to `solutions/` if `data/label_audit.jsonl` gives it
`ok`, else to `solutions-unscreened/` (`solutions-unverified/README.md`). Run `python3 dataset.py`
and commit.

## Known-hard

`1336_157`: `ProbeInsert` simulates CPython set probing; termination needs a proof that probing
visits every slot, so it keeps `decreases *` and stays in `solutions-unverified/`.

## Traps

- **`grep -q "0 errors"` also matches "10 errors".** Match
  `verifier finished with \d+ verified, 0 errors`.
- **A timed-out lemma proves nothing** — but a lemma that *calls* it still
  reports verified. Check for `time out` in the output, not just `Error`.
- `dafny verify` caps output at 5 errors; use `--error-limit 0` while diagnosing.
- A stored test outside a limit the problem statement sets is bogus: quote the limit into
  `data/constraints.jsonl` and the gates skip it. Never infer a limit from where the code fails.
- Treat any existential precondition (`requires exists k :: ...`) as suspect until `precheck.py`
  clears it.
