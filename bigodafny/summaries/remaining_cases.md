# The remaining cases

Started with 21 rows in `solutions-unverified/`. **18 now verify; 3 do not.**
`solutions/` 488 -> 506.

## What actually blocked them

Almost none were hard proofs. They were wrong questions.

| row | the real problem |
|---|---|
| `577_509` | precondition copied the problem statement (`1..1e9`); `Dfs` only needed `x >= 0` |
| `1421_53`, `1981_39`, `1981_62` | the **translation** was wrong: Python wraps a negative subscript, the Dafny had no such case |
| `1332_41`, `1563_356` | existential preconditions were banned by a rule that was itself wrong |
| `1935_61`, `1935_144` | "s is a regular bracket sequence" is stronger than either proof needs |
| `888_179` | `a_list[k] >= 1` excluded 24 inputs; only the zero-and-exactly-a-year pairing matters |
| `187_193`, `187_762`, `64_609` | carried `assume {:axiom}` and had never been looked at |

## The rule that was wrong

"Never accept an existential precondition" was a proxy. The real rule:

> A precondition must not exclude an input the original Python answers.

Excluding an input the **Python itself crashes on** is fine — the row's contract
is to reproduce that Python, and there is nothing there to reproduce.
`precheck.py` now runs the row's own `solution_code` on every violating input
and reports `py-fails` separately from `VIOLATED`. It is measured, not argued.

`1332_41`'s existential was correct all along. I rejected it twice, the second
time because it failed on a *private* test — without checking that the Python
raises `ValueError` on that same test.

## Four `assume`s, hidden for waves

`grep -rl assume` was in every audit, and every audit pointed it at
`solutions-unverified/` only. Three rows elsewhere had carried
`assume {:axiom}` since earlier waves. The file verifies, the summary says 0
errors, and the obligation is silently gone.

None was load-bearing — all four became ordinary preconditions that hold on
every input. They were unexamined, not necessary. `proofs.py` now scans the
whole corpus and exits non-zero on any hit.

## New in the prelude

| | |
|---|---|
| `PyIndex` | Python's negative subscript. 152 occur across three rows' inputs. |
| `PrefixSum` + doubling lemmas | any `\|a\|` consecutive entries of `a + a` sum to `a` |
| `JoinSplitEmptySep`, `JoinLenUniform`, `IntToStringLen` | `"1".."2777"` is exactly 10001 chars |
| `Opens`, `Closes`, `OpensPlusCloses` | bracket prefixes |

The 10001 mattered: at a bound of 1000 the precondition would have excluded 66
inputs Python handles, at 2777 still 62. Only the exact length excludes none.

## precheck learned seven shapes

`exists`; quantifiers over sequence elements; arbitrary numeric ranges;
top-level implication; top-level `||`/`&&` with a quantifier on one side;
enclosing parens; and the helpers `FloorDiv`, `FloorMod`, `SplitWs`,
`ParseInts`, `SumSeq`, `Opens`, `Closes`, `OnlyBrackets`.

Each one mattered. `OnlyBrackets` came back `unchecked` at first — and
`unchecked` would have hidden that it fails on 6 inputs, which is what sent
both bracket proofs back to be rewritten around a weaker fact.

## The three that remain

- **`1369_10`, `1369_14`** — the greedy scan is safe because leftmost-greedy
  succeeds whenever any valid selection does. That is the exchange argument, a
  theorem about the input. Anything weaker would be the loop restated as a
  hypothesis, which is `assume` wearing a different hat.
- **`1336_157`** — needs `BitAnd(x, mask) <= mask`. The bv64 fact `(a & b) <= b`
  proves instantly; carrying it across `as int` needs cast monotonicity, which
  times out at 120s. Worth knowing: the bound lemma *reports* verified while
  leaning on that timed-out lemma. A timed-out lemma proves nothing.

## The unvalidatable six

`1196_51`, `1950_45`, `1950_47` were held back as "behaviourally wrong". They
are in the `unvalidatable` split, where BigOBench's own parser raises and
`dataset.py`'s docstring already says a fail measures the parser, not the code.
All six such rows differ from their own Python — including the three that were
already sitting in `solutions/`. There is no gate that can score them.
