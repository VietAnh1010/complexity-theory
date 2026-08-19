# Demo walkthrough — three examples

Companion to `demo/status.html`. One wrong label, one precision failure that
raises a design question, one clean case modelled twice.

Everything below is `make check`-verified on Rocq 9.2: no admitted proofs,
17/17 headline theorems closed under the global context.

---

## The framing, in two sentences

BigO(Bench) labels 1.19M Code Contests solutions by profiling each at a range
of input sizes and fitting a curve. The paper is explicit that these are
"performance profiles and not theoretical complexities" — so the question is
not *can we verify their labels* (you cannot verify a curve fit) but *model a
solution, prove a bound, see whether the label agrees*.

**The disagreements are the output.**

---

## The two modelling styles

| | Writer monad (`theories/`) | Deep embedding (`theories/Alt/`) |
|---|---|---|
| Program is | a Gallina function | a syntax tree (data) |
| Cost model lives | per example, where you put `tick` | once, in the semantics |
| Loops | fuel + adequacy lemma | relational, no fuel |
| Termination | must be handled | divergence = no derivation |
| Risk | cost model re-decided per file | theorem vacuous if no derivation |
| Guard against it | — | worked witness (`run_aa`, `run_4`) |
| Cost | ~80 lines/example | ~175 lines language + ~130/example |

Both are in use. Agreement between them is a sanity check where it falls out,
not a requirement — `models_agree` was removed rather than forced.

**Neither validates the cost model.** Both encode the same judgement about
what `str.count` costs. If that reading of Python is wrong, both are wrong
together. Cross-validation catches bookkeeping errors, not modelling errors.

---

## 1 · `450_204` — the label is not an upper bound

**Problem:** 1421_C Palindromifier. **Fitted:** `O(1)`.

```python
print('3 L 2 R 2 R',len(input())*2-1)
```

**Styles available:** monad only. One line, no loop — a deep embedding would
add nothing.

**Cost model:** `len` on a built `str` is O(1) and charged nothing. But
`input()` must read the line: one tick per character.

**What we prove** (`theories/Examples/S450_204.v`):

```coq
Lemma T_eq : forall n, T n = n.

Theorem fitted_label_unsound : ~ BigO T (fun _ => 1).

Theorem true_class : Theta T (fun n => n).
```

**How.** `cost_read_line` gives `cost = length s` by a one-line induction. The
refutation goes through `not_BigO`: to refute `BigO f g` you exhibit
arbitrarily large `n` beating any constant. Here, given `c` and `n₀`, take
`n = S (max c n₀)`; then `c * 1 < n`. A disagreement is a theorem, not a
comment in a file.

**The point.** Labelled O(1), the program is Θ(n). Not a loose bound — not a
bound. Likely cause: the framework's input expansion never scaled the single
line this problem reads, so measured runtime looked flat.

**This is the only one of the six where the label is actually wrong.**

---

## 2 · `5_100` — right label, wrong question

**Problem:** 622_A Infinite Sequence. **Fitted:** `O(n)`.

```python
n=int(input())
k=1
while(n>k):
   n-=k
   k+=1
```

**Styles available:** both, and they differ in an instructive way.

- Monad (`Examples/S5_100.v`): Rocq needs structural recursion, so the loop
  takes fuel. Fuel makes any upper bound satisfiable by truncation, so
  `run_finishes` proves the fuel is never exhausted.
- Deep (`Alt/S5_100_Deep.v`): no fuel, no adequacy lemma — a truncated run
  simply is not a derivation. But the theorem is conditional on a derivation
  existing, so `run_4` builds one to rule out vacuity.

The obligation does not disappear; it changes shape.

**What we prove:**

```coq
(* upper: about sqrt(2n), stated sqrt-free *)
Theorem iters_sqrt : forall n, iters n * (iters n + 1) <= 2 * n.

(* lower: needed, or "cheap" could not be distinguished from "exits at once" *)
Theorem iters_lower : forall n j, j * j + 2 * j + 1 < n -> j <= iters n.

(* the other sizing convention *)
Theorem iters_exponential_in_bitlength :
  forall k, 1 <= k -> 2 ^ k <= iters (2 ^ (2 * k + 2)).

Lemma bitlength_witness :
  forall k, Nat.log2 (2 ^ (2 * k + 2)) + 1 = 2 * k + 3.

Example iters_table :
  (iters 64, iters 256, iters 1024, iters 4096) = (10, 22, 44, 90).
```

**How.** The invariant is `2*k*c + c*c <= 2*n + c` — the same fact stated
without subtraction, so `nia` can close the inductive step. In the monad
version the induction is on fuel; in the deep version it is on the derivation.
The lower bound needs its own induction: an upper bound alone cannot show a
loop is expensive, and without it "exponential in bit length" would be
unprovable.

`iters_table` is the non-vacuity check: √(2·4096) = 90.5 against 90 measured.

**The point.** The loop subtracts 1, 2, 3, … so it halts after ~√(2n) steps —
the fitted O(n) is a valid bound but off by a square root.

**The real question for discussion:** here `n` is the integer's *value*, not a
length. Measured against bit length the same loop is **not polynomial** —
2^k iterations on a (2k+3)-bit input. Both readings are now theorems. Under
one the loop beats the label; under the other it blows past it. The framework
takes sizes from the problem's dataclass fields, so it uses the value — but
that is not the textbook convention, and it decides the verdict.

---

## 3 · `2389_139` — the label is right, proved twice

**Problem:** ABC 044 Beautiful Strings. **Fitted:** `O(n**2)`.

```python
s=input()
ch=0
for i in s:
  if s.count(i)%2 ==1:
    ch=1
print("YNeos"[ch::2])
```

**Styles available:** both, done in parallel. This is the one where the two
styles were actually compared.

**Cost model:** one tick per character compared by `str.count`, which scans
the whole string. The outer `for` is charged only through the counts it
triggers.

**What we prove** — monad (`Examples/S2389_139.v`):

```coq
Theorem cost_beautiful : forall s,
  cost (beautiful s) = length s * length s.

Theorem fitted_label_is_tight : Theta T (fun n => n * n).
```

and independently, deep (`Alt/S2389_139_Deep.v`):

```coq
Theorem prog_cost : forall str st' c,
  evalS (init str) prog st' c -> c = length str * length str.
```

**How.**

- *Monad:* `cost_count x l = length l`, then `cost_scan s whole = |s| * |whole|`
  by induction, then `beautiful s = scan s s` collapses both factors.
- *Deep:* `guard_cost` (the guard costs one full scan) → `body_cost` (one scan,
  **and `s` is unchanged** — without that second half a later iteration could
  be scanning something shorter) → `loop_cost` by induction on the remaining
  list.

Note `prog_cost` quantifies over *every* derivation, which is why no
determinism lemma is needed: nothing cheaper can hide.

**The point.** The cost is `n²` on the nose — an equation, not an inequality —
and it does not depend on the string's contents, so the bound holds for every
input of that length rather than for a chosen family. Two independent models
reach the same answer.

---

## What to say when asked "so how many are wrong?"

**One.** Only `450_204`'s label fails to bound its program. Two more
(`5_100`, `167_177`) are `Overstated` — valid upper bounds that are
asymptotically too loose. Four of the six labels are sound.

Keeping `Overstated` separate from `NotUpperBound` matters; conflating them
overstates the finding by 3×.

## What not to claim

- **No rate.** Five of the six were picked as the *shortest* solution in their
  label class — skewed toward one-liners and I/O-bound code, plausibly exactly
  where the framework does worst. One (`167_177`) is a random draw. Counts from
  these six say nothing about the 640-record test set.
  `python3 tools/bench.py sample --n 30 --seed 20260817` produces a
  reproducible draw when someone wants to measure it properly.
- **Two √n cases is suggestive, not systematic.** `5_100` and `167_177` are
  independent programs (a triangular sum vs. an explicit `math.sqrt` bound)
  hitting the same blind spot. That is a reason to measure, not a measurement.
- **603_284 has an open gap** (Ω(n) to O(n log n)), left open rather than
  closed with a model artefact: Python's `sort` is Timsort, which is Θ(n) on
  already-sorted input where merge sort is not, so a matching lower bound
  would be false of the real program.

## Build

```bash
cd formalization
make check
#   OK: no admitted proofs
#   OK: 17/17 headline theorems closed under the global context
```

Needs Rocq 9.x. The source uses `From Stdlib Require`, so it will not build on
Coq 8.x.
