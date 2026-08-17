# formalization/

Machine-checked complexity bounds for solutions drawn from
**BigO(Bench)** ([arXiv:2503.15242](https://arxiv.org/abs/2503.15242),
[code](https://github.com/facebookresearch/bigobench),
[data](https://huggingface.co/datasets/facebook/BigOBench)), compared against
the labels its dynamic inference framework fitted.

Separate from the paper-mining pipeline in the repo root. Nothing here reads
or writes `papers/` or `dataset/`.

## What this is for

BigO(Bench) labels 1,190,250 Code Contests solutions with time and space
complexity classes. The labels are **fitted curves, not theorems** — the paper
is explicit that they are "statistically significant ground truth performance
profiles and not theoretical complexities", and reports 92% time / 84% space
agreement with human annotation on a sampled subset.

So the question is not "can we verify their labels" — you cannot verify a
curve fit. It is:

> Take a solution, model it in Coq, prove a bound, and see whether the fitted
> label agrees.

The disagreements are the output. A pile of agreeing cases is not a finding.

## Build

Needs Coq 8.18+ (`apt-get install coq`, or opam for a Rocq 9.x where the
binaries are `rocq compile` instead of `coqc` — the source here is unaffected).

```bash
make          # build everything
make check    # build, then fail if any proof is Admitted
make clean
```

## Layout

```
theories/Cost.v          the cost monad
theories/Asymptotic.v    big-O / Omega / Theta, univariate and bivariate
theories/MergeSort.v     a sort in the monad, O(n log n), with adequacy proofs
theories/Catalog.v       index: sample id -> fitted label -> proved bound -> verdict
theories/Examples/       one file per solution, named S<solution_id>.v
theories/All.v           builds everything
tools/bench.py           browse the test sets, scaffold a new example
samples/manifest.jsonl   provenance for every sample formalized here
.cache/                  downloaded test sets (gitignored, ~82MB for time)
```

## The method

Four steps per sample.

**1. Pick a sample.**

```bash
python3 tools/bench.py fetch
python3 tools/bench.py labels
python3 tools/bench.py list --label 'O(n**2)' --max-chars 300
python3 tools/bench.py show 5_100
python3 tools/bench.py scaffold 5_100
```

`scaffold` writes a stub with the source solution and the fitted label in the
header, and appends a provenance row to `samples/manifest.jsonl`. Add the new
file to `_CoqProject` and `All.v` by hand.

**2. Model the algorithm in the cost monad.** `M A` is a value paired with a
step count; `tick` charges one step, `charge n` charges `n`, and `<- ;;`
sequences and adds. The algorithm and its cost are one definition, so the cost
cannot drift from the code. This is the whole reason for the monad: a
separately-written `cost` function has nothing tying it to the algorithm, and
`cost := fun _ => 0` would make every bound provable.

**3. Prove a bound over a size-indexed family.** Convention: define
`T (n : nat) := cost (solve (List.seq 0 n))` and state the bound on `T`. If
the worst case is not attained on that family, say so in the header and use a
family that does attain it.

**4. Add a `Catalog.v` row** naming the theorem that backs it, with a verdict:

| verdict | meaning |
|---|---|
| `Tight` | fitted label is exactly the proved growth |
| `SoundUpperOnly` | matching upper bound proved, no matching lower bound |
| `SoundLoose` | correct upper bound, but not tight, or names a spurious size parameter |
| `UnsoundOver` | program is asymptotically *cheaper* than the label |
| `UnsoundUnder` | program is asymptotically *more expensive* — the label is not an upper bound |

`Catalog.v` is an index, not evidence. The `proved_bound` field is a string
and Coq does not check it against the theorem. `make check` only guarantees
nothing is admitted.

## Current entries

Five, chosen as the shortest solution in several label classes — which biases
hard toward one-liners and is **not** a random sample. See Honest limits.

| solution | fitted | proved | verdict |
|---|---|---|---|
| `2389_139` | `O(n**2)` | `cost = n²` exactly | Tight |
| `603_284` | `O(nlogn)` | `n ≤ cost ≤ 2n·log₂⌈n⌉ + 2n` | SoundUpperOnly |
| `1421_53` | `O(n+m)` | `cost = 2n`; second parameter spurious | SoundLoose |
| `450_204` | `O(1)` | `cost = n` | UnsoundUnder |
| `5_100` | `O(n)` | `cost·(cost+1) ≤ 2n`, i.e. ~√(2n) | UnsoundOver |

### Sorting

`MergeSort.v` covers any solution calling `sort` or `sorted`. All 127 of the
`O(nlogn)` records in the time test set call one or the other (measured, not
estimated), so this one module unblocks that entire class. Two things about it
are worth copying.

**Depth, not fuel.** `msort` takes a depth `d` with precondition
`length l <= 2 ^ d`. The recurrence then closes by induction on `d` alone, and
`log2_up` appears exactly once — when the top call sets
`d := log2_up (length l)`. Recursing on fuel would drag log reasoning into
every inductive step.

**Adequacy is not optional.** An upper bound on cost is vacuous if the
function skips the work: `fun l => ret l` costs nothing and satisfies every
upper bound, and so does `fun _ => ret []`. So `msort_perm` (nothing dropped)
and `msort_sorted` (actually sorted) are what make `cost_msort` mean anything.
Same reason `S5_100.v` proves its fuel is never exhausted.

## Where this can go wrong

The monad makes the cost match the model. Nothing makes the model match
Python. That gap is the entire attack surface, and it has five known holes.

**Cost model.** Where the ticks go is a judgement call, stated in each file's
header. `str.count` is a full scan; `sorted` is n log n; `x in lst` is linear
but `x in dict` is not; big-int arithmetic is not O(1). Get one wrong and the
proof is impeccable and irrelevant.

**Faithful vs. idiomatic translation.** Python list stores are O(1). Modelling
a list as a Coq `list` makes every store O(n) and turns linear programs
quadratic. `S1421_53.v` models the array as `nat -> nat` with pointwise update
for exactly this reason. Conversely, Python list *slicing* copies, and a Coq
model where it is free understates.

**What "n" means.** `S5_100.v` is the case to read. Its `n` is the numeric
value of an integer, not a length. Measured in the value the loop is √n;
measured in bit length it is exponential. The framework's size parameter comes
from the problem's dataclass fields, so it is usually a value or a collection
length, not a bit length — the files here follow that, and say so, but it is
not the textbook convention.

**Worst case vs. the measured family.** A fitted label reflects the inputs the
framework's expansion actually generated; a proof is over whatever family the
theorem quantifies. When those differ, an apparent disagreement may just be
average-case vs. worst-case. Check before recording a verdict.

**Modelling a library call with a different algorithm.** `S603_284.v` is the
case in point. Python's `sort` is Timsort; the model is merge sort. The two
agree on the worst case (both O(n log n)), so the upper bound transfers — but
Timsort is Θ(n) on already-sorted input and merge sort is not, so a matching
*lower* bound would be an artefact of the model and false of the program. That
example therefore proves only `Ω(n) ≤ cost ≤ O(n log n)` and records
`SoundUpperOnly`. Resist closing a gap like this with the model's lower bound.

## Coq trap worth knowing

Coq nests comments, so Python containing `(*` — `print(*B)`, `f(*args)` — opens
a comment inside a doc comment that never closes, and `*)` closes one early.
Both occur in real Code Contests code. `tools/bench.py` inserts a space when
scaffolding; if you paste code by hand, do the same and note it.

## Honest limits

- Five samples, picked as the shortest in their class. Short solutions are
  disproportionately one-liners and I/O-bound, which is plausibly where the
  framework's input expansion does worst. **The 2-of-5 unsound rate here says
  nothing about the benchmark's 640-sample test set** and should not be quoted
  as if it did. A defensible rate needs a random sample.
- One example (`603_284`) has an open gap between its proved lower and upper
  bounds. It is recorded as such rather than closed with a model artefact.
- Only the time test set is touched. Space is untouched; the monad counts
  steps and would need a separate high-water-mark measure for memory.
- No connection to the framework's own numeric outputs. Each record carries
  `time_curve_coefficient` and measured runtimes; comparing a proved constant
  against a fitted coefficient is a further step not attempted here.
