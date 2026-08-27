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

## What you need

- **Coq 8.18.x** and nothing newer. The pinned Iris commit and the pinned
  `iris-time-proofs` commit both require `>= 8.18 < 8.19`.
  (Later `iris-time-proofs` commits need Rocq 9 plus `coq-tlc`.)
- `git`, `make`, a shell. No OCaml work beyond what Coq already brings.
- ~2 GB of disk and ~15 min of CPU: building Iris is the long pole.
- **No sudo, no opam pins.** `setup.sh` installs std++ and Iris into
  `_deps/lib` and points `COQPATH` at it; nothing touches your system Coq
  or your opam switch.

Getting Coq 8.18:

| Platform | Command |
|---|---|
| Ubuntu 24.04 | `sudo apt-get install coq` (ships 8.18.0) |
| opam, any OS | `opam switch create iris-msort 4.14.1 && opam pin add coq 8.18.0` |
| Nix | a `coq_8_18` shell |

Check with `coqc --version` before starting.

## Build

```sh
./setup.sh          # clones + builds pinned deps into _deps, then this proof
make                # rebuild just this development afterwards
```

`make` picks up `_deps/lib` through `COQPATH` automatically. If you already
have std++ and Iris installed at exactly these commits, delete `_deps/lib`
and `make` will use yours instead.

Pinned: std++ `cafd7113`, Iris `48162f10`, iris-time-proofs `ce6fccb`.
Verified on Ubuntu 24.04 with the distro's Coq 8.18.0.

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
