# Demo walkthrough — two examples

Companion to `demo/status.html`. Two cases: a precision failure that raises a
design question, and a clean case modelled twice.

Verified with `make check` on Rocq 9.2 — no admitted proofs, 20/20 headline
theorems closed under the global context.

| # | solution | fitted | proved | outcome |
|---|---|---|---|---|
| 1 | `5_100` | `O(n)` | `cost ≈ √(2n)` | sound, too loose by a square root |
| 2 | `2389_139` | `O(n**2)` | `cost = n²` | tight |

**No label in the six-entry set is wrong.** Two are `Overstated`, one names a
spurious size parameter, three are tight or sound.

---

## The framing

BigO(Bench) labels 1.19M Code Contests solutions by profiling each at a range
of input sizes and fitting a curve. The paper calls these "performance profiles
and not theoretical complexities".

So the question is not *can we verify their labels* — a curve fit cannot be
verified. It is: model a solution, prove a bound, check whether the label
agrees.

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
not a requirement: an earlier `models_agree` theorem was dropped rather than
forced.

**Neither validates the cost model.** Both encode the same judgement about what
`str.count` costs. If that reading of Python is wrong, both are wrong together.
Cross-validation catches bookkeeping errors, not modelling errors.

---

## 1 · `5_100` — sound label, wrong question

622_A Infinite Sequence. Fitted `O(n)`.

```python
n=int(input())
k=1
while(n>k):
   n-=k
   k+=1
```

**Cost model.** One tick per loop iteration; the body is O(1) arithmetic.

**Styles.** Both, and they differ instructively.

- Monad (`Examples/S5_100.v`): Rocq needs structural recursion, so the loop
  takes fuel. A truncated loop satisfies any upper bound, so `run_finishes`
  proves the fuel is never exhausted.
- Deep (`Alt/S5_100_Deep.v`): no fuel, no adequacy lemma — a truncated run is
  not a derivation. But the theorem is conditional on a derivation existing, so
  `run_4` builds one to rule out vacuity.

The obligation does not disappear; it changes shape.

**Proved:**

```coq
(* upper: about sqrt(2n), stated sqrt-free *)
Theorem iters_sqrt : forall n, iters n * (iters n + 1) <= 2 * n.

(* lower: needed, or "cheap" could not be distinguished from "exits at once" *)
Theorem iters_lower : forall n j, j * j + 2 * j + 1 < n -> j <= iters n.

(* the other sizing convention *)
Theorem iters_exponential_in_bitlength :
  forall k, 1 <= k -> 2 ^ k <= iters (2 ^ (2 * k + 2)).

Example iters_table :
  (iters 64, iters 256, iters 1024, iters 4096) = (10, 22, 44, 90).
```

**How.**

- The invariant is `2*k*c + c*c <= 2*n + c`: the consumed-so-far fact stated
  without subtraction, which is what `nia` needs.
- The lower bound is a separate theorem. An upper bound cannot show a loop is
  expensive, and without it "exponential in bit length" would be unprovable.
- `iters_table` is the non-vacuity check: √(2·4096) = 90.5 against 90 computed.

**Why it matters.** The loop subtracts 1, 2, 3, … so it halts after ~√(2n)
steps. The fitted O(n) is a valid bound, off by a square root.

**The question for discussion.** Here `n` is the integer's *value*, not a
length. Both readings are theorems, and they disagree by more than a constant
factor:

- **By value.** `iters n * (iters n + 1) <= 2n`, so `iters n <= √(2n)`. The
  fitted O(n) is a sound upper bound but not a tight one — the cost is not
  Ω(n) (`iters_sqrt`, `fitted_label_not_tight`).
- **By bit length.** On the inputs `2^(2k+2)`, which are `b = 2k+3` bits
  wide, the loop runs at least `2^k = 2^((b-3)/2)` times, so no polynomial in
  `b` bounds the cost (`iters_exponential_in_bitlength`; non-polynomiality
  follows from it and is not itself a Rocq theorem).

The framework takes sizes from the problem's dataclass fields, so it uses the
value. That is not the textbook convention, and it decides the verdict.

---

## 2 · `2389_139` — the label is right, proved twice

ABC 044 Beautiful Strings. Fitted `O(n**2)`.

```python
s=input()
ch=0
for i in s:
  if s.count(i)%2 ==1:
    ch=1
print("YNeos"[ch::2])
```

**Cost model.** One tick per character scanned by `str.count`, which reads the
whole string. The outer `for` is charged only through the counts it triggers.

**Styles.** Both, done in parallel. This is the one where the two styles were
compared.

**Proved** — monad (`Examples/S2389_139.v`):

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

- *Monad:* `cost_count x l = length l`, then
  `cost_scan s whole = |s| * |whole|`, then `beautiful s = scan s s` collapses
  both factors.
- *Deep:* `guard_cost` (the guard costs one full scan) → `body_cost` (one scan,
  **and `s` is unchanged**) → `loop_cost` over the remaining list.
- `body_cost`'s second conjunct is needed: without it a later iteration could
  be scanning something shorter.
- `prog_cost` quantifies over *every* derivation, so no determinism lemma is
  needed — nothing cheaper can hide.

**Why it matters.** The cost is `n²` on the nose, an equation rather than an
inequality, and it does not depend on the string's contents — so the bound
holds for every input of that length, not for a chosen family. Two independent
models reach the same answer.

---

## "So how many are wrong?"

**None.** Every label in the six-entry set is a sound upper bound.

- Two (`5_100`, `167_177`) are `Overstated`: valid bounds that are
  asymptotically too loose.
- One (`1421_53`) names a size parameter the program does not depend on.
- Conflating `Overstated` with `NotUpperBound` would overstate the findings.

## What not to claim

- **No rate.** Six entries say nothing about the 640-record test set, and
  selection was not uniform over it. `tools/bench.py sample` is what a real
  measurement would use.
- **Two √n cases are suggestive, not systematic.** `5_100` and `167_177` are
  independent programs (a triangular sum vs. an explicit `math.sqrt` bound)
  hitting the same blind spot. A reason to measure, not a measurement.
- **`603_284` has an open gap** (Ω(n) to O(n log n)), left open rather than
  closed with a model artefact: Python's `sort` is Timsort, which is Θ(n) on
  already-sorted input where merge sort is not, so a matching lower bound would
  be false of the real program.

## Build

```bash
cd formalization
make check
#   OK: no admitted proofs
#   OK: 20/20 headline theorems closed under the global context
```

Needs Rocq 9.x. The source uses `From Stdlib Require`, so it will not build on
Coq 8.x.
