# Prove one batch of rows against its complexity label

Your rows are the ones listed in `{{BATCH}}/slice_{{SLICE}}.jsonl`. Read that
file first; each line gives the solution id, its path, and its label.

Each assigned row behaves correctly and passes `dafny verify`. What it has
never had is a **proof of its complexity label**. You supply one: a ghost step
counter with a proved upper bound.

## Setup

```bash
cd /home/user/complexity-theory/bigodafny
export PATH="$PATH:/root/.dotnet/tools"
dafny verify <file> --solver-path /usr/local/bin/z3 --verification-time-limit 30
```

## Where your work goes — read this twice

You **copy** the row, you do not edit it in place.

    solutions/<pid>/<sid>.dfy      the original. NEVER modify it.
    solutions-proved/<pid>/<sid>.dfy   your instrumented copy. Create it.

`solutions-proved/` is an overlay, not a move. Both files exist afterwards.
Fix the `include "../../prelude.dfy"` path if the nesting differs.

## The shape

```dafny
method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| + 2          // O(n)
{
  steps := 1;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps == 2 * i + 1
    decreases |a_list| - i
  {
    i := i + 1;
    steps := steps + 2;
  }
  output := "";
  steps := steps + 1;
}
```

`steps` is `ghost`, so it is erased at compile time and the emitted Python is
unchanged. Add `steps` to every helper the row calls, as a ghost out-parameter
with its own `ensures`.

## The charges — these are stipulated, not measured

Charge **1** for each: `int` arithmetic and comparison, `s[i]`, `|s|`, and one
unit of loop overhead per iteration.

| operation | charge |
|---|---|
| `s[i := v]`, `s + [x]`, `s[a..b]` | `1` |
| `s + t` | `\|t\|` |
| `m[k]`, `k in m`, `m[k := v]`, `\|m\|` | `1` |
| `m.Keys`, `m.Values`, `m.Items` | `\|m\|` |
| `x in s`, `s + {x}` on `set<T>` | `1` |
| iteration over a set | `\|s\|` |
| `multiset(s)` | `\|s\|` |
| `multiset(a) == multiset(b)` | `\|a\|+\|b\|` |
| `Join(parts, sep)` | `SumLen(parts) + \|parts\|` |
| a recursive prelude function over a seq or string | its length |
| a call to a helper | the helper's `steps` |

Do **not** charge `|s|` for `s[i := v]`. That was the old backend-derived model
and it was retired; old files in `solutions-proved/` still use it.

## Constants do not matter

The label is asymptotic. `steps <= 7*n + 12` proves O(n). Take whatever
constant the invariant supports; never tune one to look tight.

## Logarithmic bounds

Dafny has no `log`. Define one, and **match its rounding to the code's**:

```dafny
ghost function Log2(x: nat): nat  decreases x     // loop does m := m / 2
{ if x <= 1 then 0 else 1 + Log2(x / 2) }

ghost function CeilLog2(n: nat): nat  decreases n // recursion splits into ceil(k/2)
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }
```

Pick the wrong one and the inductive step is false at some small `k` — floor-log
fails at `k = 3` for a split — and nothing you add will close it.

**Isolate every multiplication into its own lemma.** Z3 is bad at nonlinear
arithmetic; an argument with the multiplications inline times out where the same
argument with `MulMonoRight` and `MulDistrib` as separate lemmas finishes in
seconds.

## Rules you may not break

1. **No `assume`.** Not anywhere, not temporarily. `proofs.py` greps the whole
   corpus for it and fails.
2. **No `decreases *`.**
3. **Do not change what the row computes.** You add ghost state, `ensures`,
   `invariant`, `decreases`, `assert`, and lemmas. Nothing else.
4. **Do not touch** `solutions/`, `validate.py`, `difftest.py`, `verify_all.py`,
   `precheck.py`, `proofs.py`, or anything in `data/`.
5. **If your proved bound exceeds the label, keep the proof and record it.**
   Never weaken a proof to match a label. The label is a regression over
   profiling runs; a proof holds for every input.

## Your bound is an upper bound — say what it does, not what it feels like

An upper bound can **confirm** a label or **fail to confirm** it. It cannot
refute one. A proved `O(n**2)` on a row labelled `O(nlogn)` does not mean the
label is wrong; it means you did not reach the label. Refuting a label takes a
**lower** bound, and nothing in this campaign produces one.

So record `relation` from exactly this vocabulary:

| value | when |
|---|---|
| `confirms` | your bound is within the label's class |
| `looser-slack` | you used a loose scaffold and did not attempt the tight bound |
| `looser-structural` | your proof exposes a real cost the label omits |
| `tighter-costmodel` | your bound is below the label because the charge table costs something CPython does not — most often `int` arithmetic on values that outgrow a machine word |
| `tighter-translation` | your bound is below the label because the Dafny uses a cheaper algorithm than the Python, not because the label is loose |
| `contradicts` | the row provably cannot meet the label — a literal in the source forces more work than the label allows |

`contradicts` needs a reason naming the construct in the source. Do not reach
for it because a bound came out large.

A bound **below** the label is not automatically a tighter reading of the row.
Before recording one, read the Python: if it sorts and your Dafny compares
multisets, or if it multiplies numbers that grow past a machine word, the gap
is the translation or the charge table, not the label. Say which.

## Value versus size — a settled convention

A loop bounded by an input **value** counts: the value is a parameter of the
bound, written out like any other. Do not treat a capped input value as a
constant; the hidden factor is large enough that the resulting label predicts
nothing. A quantity **fixed in the source** is a constant however large.

## Bounds, per row — hard

- **3 attempts.** One attempt = one edit followed by one `dafny verify`.
- **5 minutes** wall clock, including verifier time.
- Out of either → delete **your own row's** partial copy from
  `solutions-proved/`, record `unresolved` with the reason, move on.
- **Delete `solutions-proved/<pid>/<sid>.dfy` for YOUR `<sid>` and nothing
  else.** Never remove the directory. Two verified proofs were destroyed this
  way in one campaign: an agent abandoning `2914_3` took `2914_264` with it,
  and one abandoning `750_14` took `750_51`. Those are different solutions of
  the same problem, with their own labels and their own proofs.

**Most rows will not close in this budget, and that is the expected result.**
An accurate `unresolved` is the deliverable; a proof that does not verify is
worthless.

## What to write back

Append **one JSON object per line** to your own
`{{BATCH}}/traj_{{SLICE}}.jsonl` — that is what JSONL means, and every tool
that reads the file assumes it. Do not pretty-print across several lines: one
slice did, and its 16 rows arrived as 59 lines that nothing could parse.
Never write to another agent's file, and never to any other file in that
directory.

```json
{"solution_id":"1053_38","label":"O(n)","outcome":"proved",
 "bound":"3 * |a_list| + 4","relation":"confirms","relation_reason":"",
 "attempts":[{"n":1,"action":"ghost steps + loop invariant steps == 3*i+1","outcome":"failed","note":"invariant not maintained across the inner append"},
             {"n":2,"action":"charged s + [x] as 1, not |s|","outcome":"verified","note":""}],
 "attempts_used":2,"seconds":140,"why_failed":null}
```

`outcome` is `proved` or `unresolved`. On `unresolved`, `why_failed` names the
obstacle in one sentence — which invariant would not hold, or which
multiplication the solver would not do. Not "ran out of attempts". Leave
`relation` as `null` on an unresolved row. Fill `relation_reason` whenever
`relation` is not `confirms`.

## Reporting

Be concise. No preamble, no per-command narration. Final message ≤ 8 lines:
counts proved / unresolved, any row whose `relation` is not `confirms`, and the
single most common obstacle. The trajectory file is the record — do not repeat
it in chat.
