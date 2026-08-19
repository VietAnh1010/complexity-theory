# formalization/

Machine-checked complexity bounds for solutions from **BigO(Bench)**
([arXiv:2503.15242](https://arxiv.org/abs/2503.15242),
[code](https://github.com/facebookresearch/bigobench),
[data](https://huggingface.co/datasets/facebook/BigOBench)), compared against
the labels its dynamic inference framework fitted.

Separate from the paper-mining pipeline in the repo root; reads and writes
nothing under `papers/` or `dataset/`.

## What this is for

BigO(Bench)'s labels are **fitted curves, not theorems** — the paper calls them
"statistically significant ground truth performance profiles and not
theoretical complexities", at 92% time / 84% space agreement with human
annotation. So the question is not "verify their labels"; you cannot verify a
curve fit. It is: model a solution, prove a bound, see whether the label
agrees. **The disagreements are the output.**

## Build

Rocq 9.x. Source uses `From Stdlib Require`, so it does not build on Coq 8.x.

```bash
make          # build everything
make check    # build + gate: no admitted proofs, no axioms
make clean
```

`make check` is the gate. It fails on a build error, on any `Admitted`, and —
via `tools/check_axioms.sh` — if any headline theorem turns out to depend on
an axiom.

## Layout

```
theories/Cost.v          the cost monad
theories/Asymptotic.v    BigO / BigOmega / Theta, univariate and bivariate
theories/MergeSort.v     a sort in the monad, O(n log n), with adequacy proofs
theories/Catalog.v       index: sample id -> label -> proved bound -> verdict
theories/Examples/       one file per solution, named S<solution_id>.v
theories/Alt/            a second, independent model — deep embedding
tools/bench.py           browse the test sets, scaffold a new example
samples/manifest.jsonl   provenance for every sample formalized here
.cache/                  downloaded test sets (gitignored, ~82MB for time)
```

## Entries

Six. The first five were each the shortest solution in their label class —
**not** a random sample. `167_177` is the first drawn at random (see Method
step 1). Selection method is recorded per row in `samples/manifest.jsonl`.

| solution | problem | fitted | proved | verdict | file |
|---|---|---|---|---|---|
| `2389_139` | p04012 ABC 044 Beautiful Strings | `O(n**2)` | `cost = n²` exactly | Tight | `Examples/S2389_139.v` |
| `603_284` | 1041_A Heist | `O(nlogn)` | `n ≤ cost ≤ 2n·log₂⌈n⌉ + 2n` | SoundUpperOnly | `Examples/S603_284.v` |
| `1421_53` | p02899 ABC 142 Go to School | `O(n+m)` | `cost = 2n`, 2nd param spurious | SoundLoose | `Examples/S1421_53.v` |
| `450_204` | 1421_C Palindromifier | `O(1)` | `cost = n` | NotUpperBound | `Examples/S450_204.v` |
| `5_100` | 622_A Infinite Sequence | `O(n)` | `cost·(cost+1) ≤ 2n`, and ≥ 2^k on 2k+3 bits | Overstated | `Examples/S5_100.v` |
| `167_177` † | 1184_A1 Heidi Learns Hashing | `O(n)` | `cost ≤ √n` | Overstated | `Examples/S167_177.v` |

† drawn at random, not shortest-in-class.

| verdict | meaning |
|---|---|
| `Tight` | label is exactly the proved growth |
| `SoundUpperOnly` | matching upper bound proved, no matching lower bound |
| `SoundLoose` | correct upper bound, not tight, or names a spurious size parameter |
| `Overstated` | label *is* a valid upper bound, but asymptotically too large |
| `NotUpperBound` | program is more expensive than the label — the label is wrong |

Only `NotUpperBound` means the label is incorrect. `Overstated` is a precision
failure: O(n) does bound a √n loop, it just says nothing useful. Keeping these
apart matters — four of the six labels are sound.

`Catalog.v` is an index, not evidence: its `proved_bound` is a string that Rocq
does not check against the theorem. `make check` only guarantees no proof is
admitted.

## Method

**1. Pick a sample.**

```bash
python3 tools/bench.py fetch
python3 tools/bench.py labels
python3 tools/bench.py list --label 'O(n**2)' --max-chars 300
python3 tools/bench.py sample --n 30 --seed 20260817   # reproducible draw
python3 tools/bench.py scaffold 5_100
```

Prefer `sample` over `list` for anything meant to support a rate. `list` sorts
by length, which is how the first five were picked and why they cannot.

`scaffold` writes a stub carrying the source solution and fitted label, and
appends provenance to `samples/manifest.jsonl`. Add the file to `_CoqProject`
and `All.v` by hand.

**2. Model it in the cost monad.** `M A` pairs a value with a step count;
`tick` charges one, `charge n` charges `n`, `<- ;;` sequences and adds. The
algorithm and its cost are one definition, so cost cannot drift from code — a
separately-written `cost := fun _ => 0` would prove every bound.

**3. Prove a bound over a size-indexed family**, by convention
`T (n : nat) := cost (solve (List.seq 0 n))`. If the worst case is not attained
on that family, say so in the header and use one that is.

**4. Add a `Catalog.v` row** naming the theorem that backs it.

## Where this can go wrong

The monad makes cost match the model. Nothing makes the model match Python.
That gap is the whole attack surface; five known holes.

- **Cost model.** Where ticks go is a judgement call, stated in each file's
  header. `str.count` scans; `x in lst` is linear but `x in dict` is not;
  big-int arithmetic is not O(1). Get one wrong and the proof is irrelevant.
- **Faithful vs. idiomatic translation.** Python list stores are O(1);
  modelling the list as a Rocq `list` makes each store O(n) and turns linear
  programs quadratic. `S1421_53.v` uses `nat -> nat` with pointwise update for
  this reason. Conversely Python slicing copies, and a free model understates.
- **What "n" means.** In `S5_100.v` and `S167_177.v` it is an integer's
  *value*, not a length. `S5_100.v` now proves both readings:
  `iters_sqrt` gives ~√(2n) in the value, and
  `iters_exponential_in_bitlength` gives ≥ 2^k iterations on a (2k+3)-bit
  input. Under one convention the loop beats the fitted O(n); under the other
  it is not polynomial at all. The framework takes sizes from the dataclass
  fields, so these files follow that — not the textbook convention.
- **Worst case vs. measured family.** A label reflects the inputs the
  framework's expansion generated; a proof reflects the family quantified over.
  An apparent disagreement may be average- vs. worst-case.
- **Modelling a library call with a different algorithm.** `S603_284.v`:
  Python's `sort` is Timsort, the model is merge sort. They agree on the worst
  case so the upper bound transfers, but Timsort is Θ(n) on sorted input where
  merge sort is not, so a matching *lower* bound would be a model artefact.
  Hence `Ω(n) ≤ cost ≤ O(n log n)` with the gap left open.

## Sorting

`MergeSort.v` covers `sort` / `sorted`. All 127 `O(nlogn)` records in the time
test set call one of them (measured), so it unblocks that class.

- **Depth, not fuel.** `msort` takes depth `d` with precondition
  `length l <= 2 ^ d`, so the recurrence closes by induction on `d` alone and
  `log2_up` appears only at `msort_top`.
- **Adequacy is required.** `fun l => ret l` and `fun _ => ret []` both cost
  nothing and satisfy every upper bound, so `msort_perm` and `msort_sorted` are
  what make `cost_msort` mean anything. Same reason `S5_100.v` proves its fuel
  is never exhausted.

## Alternative model: deep embedding

`Alt/Deep.v` is a tiny imperative language with a step-counting big-step
semantics. `Alt/S2389_139_Deep.v` and `Alt/S5_100_Deep.v` re-model two of the
solutions in it, sharing no definitions with the monad versions and reaching
the same bounds.

The difference that matters: in the monad the cost model is a per-file
judgement (where the `tick`s go); in the deep embedding it is one rule in the
semantics, `EV_Count`, reviewed once and reused by every program.

- Relational, so no fuel and no termination obligation — a diverging program
  simply has no derivation. Compare `S5_100.v`'s `run_finishes`.
- Cost theorems quantify over *every* derivation, so no determinism lemma is
  needed to rule out a cheaper one.
- `SWhile` is now in the language, so `Alt/S5_100_Deep.v` re-proves the √n
  bound with **no fuel and no adequacy lemma** — `S5_100.v` needs
  `run_finishes` only because a fuel-truncated loop satisfies any upper bound
  for free. Here a truncated run simply is not a derivation.
- The price: the semantics is no longer total, so `prog_sqrt` is conditional
  on a derivation existing. `run_4` is a worked witness, which is what keeps
  the theorem from being vacuous.
- Cost: ~175 lines of language + ~130 per example, against 78 for the monad
  version.

Agreement between the two styles is a sanity check, not a requirement: it is
recorded where it falls out, and not forced where it does not. It would not
validate the cost model anyway — both styles encode the same judgement about
what `str.count` costs, so a wrong reading of Python is wrong in both.

## Rocq trap

Rocq nests comments, so Python containing `(*` — `print(*B)`, `f(*args)` —
opens a comment inside a doc comment that never closes, and `*)` closes one
early. Both occur in real Code Contests code. `tools/bench.py` inserts a space
when scaffolding; do the same and note it when pasting by hand.

## Limits

- **No rate is claimed.** Five of six were the shortest in their class, which
  skews toward one-liners and I/O-bound code — plausibly where the framework's
  input expansion does worst. Counts from these six say nothing about the
  640-record test set. `bench.py sample` exists to fix this; one entry
  (`167_177`) is drawn that way so far.
- Both `Overstated` verdicts are √n loops labelled O(n), reached by different
  routes (a triangular sum, an explicit `math.sqrt` bound). Suggestive of a
  systematic blind spot, but two cases is not evidence of one.
- `603_284` has an open gap between its proved lower and upper bounds,
  recorded rather than closed with a model artefact.
- Time test set only. Space is untouched: the monad counts steps and would
  need a separate high-water-mark measure.
- No comparison against the framework's numeric outputs. Each record carries
  `time_curve_coefficient` and measured runtimes; relating a proved constant to
  a fitted coefficient is a further step not attempted.
