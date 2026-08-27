# Merge sort, verified `O(n log n)` in Iris with time credits

A worked demo: HeapLang merge sort, proved correct *and* proved to run in
`O(n log n)` steps, in one separation-logic proof. Machine-checked, no admits.

Outside the dataset pipeline — this directory is a standalone Coq development.

## What is proved

`theories/MsortProof.v`, all statements checked by `coqc`:

- `msort_spec` — given `220 * (n * ⌈log₂ n⌉) + 40` time credits, `msort v`
  returns a `Sorted Z.le` permutation of the input list.
- `msort_prgm_timed_spec` — end-to-end, via the logic's adequacy theorem:

  ```coq
  adequate NotStuck (msort_prgm n) σ (λ v _, v = #(n * (n + 1) / 2))
  ∧ bounded_time (msort_prgm n) σ (msort_prgm_cost n)
  ```

  where `msort_prgm n = sum_list (msort (make_list #n))` and
  `msort_prgm_cost n = (4 + 7n) + (220 * (n * ⌈log₂ n⌉) + 40) + (4 + 13n)`.

`bounded_time e σ m` is the library's definition: **every** reduction sequence
from `([e], σ)` has at most `m` steps. Not a claim about a cost monad — a claim
about the operational semantics.

`Print Assumptions msort_prgm_timed_spec` reports one axiom, `lang.word_size`,
a parameter of the library's HeapLang. Nothing else.

## How the cost model works

- Credits come from `iris-time-proofs` (Mével, Jourdan, Pottier, ESOP 2019).
- `$n` (`TC n`) is a resource; `{$1} tick() {True}` is the only way to step.
- The *tick translation* `«e»` inserts a `tick` before every reduction step.
- So specs are stated about `«e»`, and adequacy transfers the bound to `e`.
- One credit per beta-step, load, store, alloc, projection, injection, primop.

## The three specs, and where the log comes from

| Lemma | Credits required |
|---|---|
| `split_list_spec` | `40n + 40` |
| `merge_list_spec` | `40n + 40` |
| `msort_spec` | `220 * (n * ⌈log₂ n⌉) + 40` |

The recurrence is closed in `theories/MsortMath.v`, independent of Iris:

- `msort_cost_step` — for `a + b = n`, `b ≤ a ≤ b + 1`, `2 ≤ n`, `c + d + E ≤ K`:
  `(c·n + d) + cost(a) + cost(b) ≤ cost(n)`, where `cost(n) = K·n·⌈log₂ n⌉ + E`.
- The halving step is `Nat.log2_up a + 1 ≤ Nat.log2_up n` when `2a ≤ n + 1`.
- `split2` splits by dealing alternate elements, so `a` and `b` are the halves.

## Build

```sh
./setup.sh          # clones + builds pinned deps, then this development
make                # rebuild just this development
```

Tested on Ubuntu 24.04 with the distro's Coq 8.18 (`apt-get install coq`).
Pinned: stdpp `cafd7113`, Iris `48162f10`, iris-time-proofs `ce6fccb`.
`setup.sh` installs stdpp and Iris into Coq's user-contrib.

## Caveats, stated plainly

- Constants are generous, not tight — enough credits, not the exact count.
- The bound uses `Nat.log2_up`, i.e. `⌈log₂ n⌉`; no real-valued asymptotics.
- No `O(·)` abstraction: the bound is a concrete closed form, as in the
  original union-find development. Big-O machinery is a separate layer
  (Guéneau, Charguéraud, Pottier, ESOP 2018).
- `split_list` allocates fresh cells and drops the input list; Iris is affine,
  so the old cells are simply discarded, not freed.
- Sequential. Parallel work/span credits are a different logic.

## Provenance

- Time credits in Iris: <https://iris-project.org/pdfs/2019-esop-time.pdf>
- Library: <https://gitlab.inria.fr/gmevel/iris-time-proofs>
- The library's own examples cover union-find, thunks, and Okasaki queues;
  merge sort was not among them, which is why this exists.
