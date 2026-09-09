# What blocks a complexity proof, and why

Companion to `complexity_proofs.md`, which records what was proved. This
records what was **not**, with the reason, so the next wave does not re-derive
it. Counts are over the 602 rows in `solutions/` and `solutions-inexact/` that
carry no proof yet.

Two kinds of entry:

- **blocked** — the obstruction is in the cost model or the toolchain. Attempting
  the row again without fixing it wastes the attempt.
- **attempted and wrong** — a proof was produced and does not say what it looks
  like it says. These are the dangerous ones; each has a rule attached.

---

## Blocked: the cost of a primitive is unknown or undercharged

### `Join` / `JoinInts` — 164 rows

Measured superlinear (~L^1.2) in Dafny 4.11.0's Python backend; see
`COMPLEXITY.md`. Charging `SumLen(parts) + |parts|` **undercharges** it, and an
undercharged operation is the one error that makes a proof claim something
false. Charging it quadratically is sound but yields a bound so loose the label
is unreachable.

Every row whose output is one line per input item hits this. It is the single
largest blocker in the corpus — 27% of unproved rows — and it is a property of
the prelude, not of any row. `171_82`, `89_463`, `2602_57` and `378_20` are each
provable but for this term.

**Unblocks it:** a linear-time join in `prelude.dfy` (accumulate into an
`array<char>`, one pass), or a measurement pinning the exponent well enough to
charge it honestly. This is the highest-value single change available.

### `map<K,V>` — 22 rows, and `set<T>` — 22 rows

`set<T>` insertion is measured O(|s|) — `CLAUDE.md` has the numbers, and this
session reproduced them (n=2000/4000/8000 at .058/.112/.319s). `map` is
**unmeasured**. Both are backed by frozen collections that the runtime rebuilds
per insert, so a `map` insert is likely O(|m|) too, but "likely" is not a charge.

A row building either inside a loop cannot be proved at its label without
knowing the real cost, and if the cost is O(|s|) the row's translation carries
an extra factor of n and the label is wrong for the *translation* rather than
for the Python.

**Unblocks it:** measure `map` insert and lookup the way `set` was measured.
Cheap — one microbenchmark, an hour at most.

### Arbitrary-precision integer arithmetic — 2 rows

`1073_645` computes `Factorial(n+1)` and divides. The charging convention grants
`int` arithmetic 1 step, which is true for machine-word values and false here:
`n!` has Θ(n log n) bits, so each multiplication is superlinear in n and the
loop is not O(n). The row is labelled `O(n**2)`, which may well be right — but
the convention cannot express the reason, so a proof under it would be counting
the wrong thing.

This is the one place the convention is knowingly unsound rather than merely
loose. It is confined to rows whose values grow with n; every other row's
integers stay bounded by the problem's stated constraints.

**Unblocks it:** a bit-length term in the charge for `*` and `/`. Large change,
2 rows — not worth it yet, but it must not be forgotten, because a proof written
under the current convention for one of these rows would be wrong, not loose.

### `multiset` — 2 rows

`1243_0` decides anagram-equality with `multiset(s1) != multiset(s2)`.
Construction cost is unmeasured, same family as `set`.

---

## Blocked: no bound exists to prove

### `decreases *` — 19 rows

Dafny accepts these with termination unproved. `310_121` factors `n` by trial
division from 2 upward; `2482_13`, `1972_295` and 16 others have the same shape.
No step bound can be stated for a loop that is not known to terminate.

Not a defect: the Python terminates for the inputs the problem admits, and the
loop count depends on a *value*, not a size. `827_148` is the pattern for
handling it — take the problem's stated numeric cap as a precondition, check it
with `precheck.py`, fold it into the constant, and say plainly that the label
assumes the same cap silently. That works only where the statement declares a
cap. Where it does not, the row is genuinely unbounded in the input size.

---

## Attempted and wrong: rules paid for in retracted work

### An upper bound cannot refute a label from below

A ghost step counter proves `steps <= f(n)`. That contradicts a label only when
`f` is **strictly tighter** than the label. Proving `O(n**2)` against an `O(n)`
label establishes nothing — an O(n) program also satisfies a quadratic bound.

In the `pilot1` experiment 8 agent runs wrote `refutes`; **6 did not meet this
bar**. The mechanism those agents described may be real; it is not what their
artifact proved. The agent's verdict is its belief, the direction of the bound
is the result.

### A constant bound on a program that loops over its input is degenerate

`pilot1` blind/`2381_176` proved `steps <= 20000000000` against an `O(n)` label.
True, verified, and vacuous: the constant is the problem's numeric cap folded in.
Flag it, never count it as a refutation.

### Overcharging invents disagreements — and it did, 6 times

Six of `pilot1`'s 14 label disagreements carry the drift tag `append-in-loop`:
an agent charged `s := s + [x]` its documented O(|s|), landed on a quadratic
bound, and recorded a disagreement with an `O(n)` or `O(nlogn)` label.

**That charge was wrong.** This session measured it: the Python backend defers
the concat, so append-only accumulation is O(1) amortised and only an element
read between appends forces a flatten. The rows are linear; the bounds were
artifacts of the convention.

Affected: `794_794` (both arms), `2650_140` (both arms), `1827_44` (blind),
`378_20` (labeled). Those six verdicts should be regraded under the corrected
convention before any of them is cited as a finding.

The general rule: **undercharging proves a false bound, overcharging invents a
false disagreement.** Both are counting errors, and neither is visible to
`dafny verify`.

### A proof describes the Dafny, not the Python the label was measured on

`305_284`'s translation replaces the Python's `for x in range(p, q)` loop with a
closed form — correct, since the guard is monotone in `x`, and the loop's
iteration count depends on values rather than sizes. But BigOBench measured its
label on the *Python*, so a bound proved about this Dafny does not transfer.

Not attempted for that reason. The same caution applies to any row where the
translation restructured across a complexity class — `CLAUDE.md` § *Translate
the algorithm* forbids that, and this is the proving-side consequence of the
same rule.

### A bound must hold on the whole domain, including inputs no test visits

`1756_577` verified at `3n² + 4n + 3` for every n the tests supply and failed
the postcondition for **n = -1**, where the quadratic dips below the 3 steps the
method takes when the loop never runs. The constant went to 7.

Constants are free, so the fix is trivial — but the failure is worth recording
because it is the honest form of an error that is otherwise silent: `1254_187`
carried `requires n >= 1` for two waves to avoid exactly this, and that
precondition excluded 48 of its own stored inputs. Widen the constant; do not
narrow the domain.

---

## Cost of a proof, measured

`pilot1` records `dafny` invocations per example as `difficulty_measured`.

| difficulty_static | n | proved | mean dafny calls |
|---|---|---|---|
| 1 | 4 | 4/4 | 2.8 |
| 2 | 16 | 13/16 | 2.1 |
| 3 | 9 | 7/9 | 2.7 |
| 4 | 8 | 3/8 | 5.0 |

Difficulty declared before the run from label-free features tracks the outcome:
the proof rate falls from 100% to 38% across the range and the solver-call count
roughly doubles. The prediction is not circular — `difficulty_static` was
written down before any agent ran.

In this session's manual track, 21 rows were proved in 21 attempts, at 1.2
`dafny verify` calls each. That rate is not comparable to the agent arms: the
rows were selected for provability, and rows hitting the obstructions above were
set aside rather than attempted.
