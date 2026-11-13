FIRST ACTION: call the Skill tool with skill="my-concise". Follow it for all
prose. Code is exempt.

# Task
Make about 20 existing Dafny translations pass `dafny verify` with no
`decreases *`. They already pass their tests. Do NOT change what they compute.

Working directory: bigodafny/ (from the repository root)
Manifest: batches/verify-clean/w_{{NN}}.txt -- one row path per line, e.g.
`solutions-unscreened/64/64_1063.dfy`. Edit each file where it is; never move it.
`dafny` and `z3` are on PATH.

    dafny verify <path> --verification-time-limit 30 --error-limit 0

A row is done when the output says `verifier finished with N verified, 0 errors`
(note: `10 errors` also contains "0 errors"; read the whole line), no
`time out`, and the file has no `decreases *`.

# What you are fixing
Dafny raises obligations with no specification written: every `s[i]` needs
`0 <= i < |s|`, every `/` needs a non-zero divisor, every loop needs a
`decreases` that decreases. Some rows instead opt out with `decreases *`;
replace it with a real `decreases` clause.

# If the row already has a proof
If `solutions-proved/<PID>/<SID>.dfy` or `solutions-proved/value-bounded/<PID>/<SID>.dfy`
exists, it already proves termination and safety on the same code. Copy its
`decreases` clauses, loop invariants and lemma calls into the row. Do NOT copy
the ghost `steps` counter, its updates, or its `ensures steps <= ...`.

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
   need in MEMBERSHIP form (`forall x :: x in arr ==> P(x)`).
9. `Prelude.MaxSeq`/`MinSeq` require `|s| > 0` and have NO membership
   postcondition. If you need `MaxSeq(s) in s`, prove it locally.
10. A verifier time-out: add `{:isolate_assertions}` to the method, or split
    a long method's facts into small lemmas.
11. Python wraps a negative subscript; Dafny faults. If the Python reads
    `a[-1]`-style indexes, the fix is `Prelude.PyIndex`, not a `requires`.

# Rules, in priority order
- **NEVER use `assume`, in any form.** A row left unverified is strictly better.
- **NEVER use `decreases *`.**
- **Prefer an invariant to a precondition.** An invariant proves the code
  safe; a precondition narrows the contract until it is.
- Any `requires` you add must be something the PROBLEM guarantees -- read
  the Python and the problem description in `data/tasks.jsonl` if needed. The
  parent checks every added precondition against every stored test input and
  reverts ones that fail.
- No `var` binding inside a `requires`: state it over the parameters.
- Do not change the algorithm, the signature, or any computed value.
- Ghost code (invariants, lemmas, asserts, ghost variables) is allowed.

# Loop
1. Verify, read the error, add the invariant, re-verify.
2. ~10 tool calls per row. If it will not verify, LEAVE IT AS IT WAS
   (`git checkout -- <path>`) and report a one-line diagnosis.
3. After every ~5 rows changed, confirm behaviour is unchanged:
       python3 validate.py --only SID1 SID2 ... --out-prefix vc{{NN}}_
   For `loose` rows validate.py cannot score, use
       python3 difftest.py --only SID1 SID2 ...
   (`agrees` is the pass). Run both with `.venv/bin/python3`. If a row
   regresses, revert it.

# Hard rules
- NEVER git add/commit/push/mv. `git checkout --` on your own files is allowed.
- Edit ONLY the files in your manifest. NEVER edit prelude.dfy, any *.py,
  anything under data/, batches/, or solutions-proved/.

# Report (concise)
- how many rows now verify with no `decreases *`
- every `requires` you added: row, method, clause
- rows you could not fix, one line each with the blocking error
