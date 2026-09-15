# Migrate `prelude.dfy` call sites to the Dafny standard library

`prelude.dfy` is 453 lines and exports 51 names that were written before anyone
checked what `Std` already provides. This task replaces the ones `Std` covers
*better*, leaves the ones it covers *worse*, and records the difference.

**Read this whole file before editing anything.** The measurements below were
taken on this toolchain (Dafny 4.11.0, CPython, the Python backend) and three of
them reverse the obvious decision. `Std.Strings.ToNat` — the swap that prompted
this task — is one of the three that must **not** be made.

## What the gates will do to you

Every row carries a BigOBench complexity label measured on the original Python.
A swap that changes the emitted Python's cost class breaks the dataset's only
claim, and **no gate catches it**: `validate.py` and `difftest.py` compare
stdout, and the tests are small enough that a quadratic parser still passes.

So the acceptance condition for each swap is two things, not one:

1. `validate.py` (strict rows) / `difftest.py` (loose rows) still pass.
2. The emitted Python for the swapped function is in the **same cost class**,
   measured, not assumed. The table below is that measurement for every
   candidate; if you add a candidate, measure it the same way.

Neither gate may be edited. `bigodafny/CLAUDE.md` § "Two gates".

## Measured verdicts — do not re-derive, do not override without re-measuring

Timings are the emitted Python called directly, CPython default settings.
"rows" is how many of the 443 files in `solutions/` contain a call.

| prelude | rows | Std counterpart | verdict |
|---|---|---|---|
| `ParseInt` | 10 | `Std.Strings.ToNat` | **DO NOT SWAP** |
| `ParseIntFrom`, `ParseInts` | 6 | — | keep (built on `ParseInt`) |
| `MaxSeq`, `MinSeq` | 20 / 10 | `Seq.Max`, `Seq.Min` | **DO NOT SWAP** |
| `IntToString` | 317 | `Std.Strings.OfInt` | swap only where the integer can reach ~1000 digits; see below |
| `SortInts`, `SortStrings`, `Sort` | 50 / 2 / 52 | `Seq.MergeSortBy` | **SWAP** — equal cost, and Std brings the sortedness and permutation lemmas |
| `Merge` | 8 | `Seq.MergeSortedWith` | swap with `Sort`; it is `MergeSortBy`'s helper |
| `Join`, `JoinInts` | 74 | `Seq.Join` | **SWAP** — equal cost |
| `AbsInt` | 20 | `Std.Math.Abs` | **SWAP** — one-liner either way, no cost question |
| `MaxSeqFrom`/`MinSeqFrom` two-arg max | — | `Std.Math.Max`, `Min`, `Max3`, `Min3` | **SWAP** at the scalar call sites |
| `Repeat` | 14 | `Seq.Repeat` | **keep.** Different function: `Prelude.Repeat(s, n)` repeats a *string* n times (Python `s * n`); `Seq.Repeat(v, n)` repeats one *element*. See the note below |
| `FloorDiv`, `FloorMod` | 33 / 16 | — | **keep.** Std's arithmetic is Euclidean like Dafny's `/` and `%`; Python's `//` and `%` floor. That divergence is the whole reason these exist |
| `Gcd` | 6 | — | **keep.** `Std` has no gcd (0 occurrences in the library source) |
| `BitOr`, `BitAnd`, `BitXor` | 1 | — | **keep.** No bitwise helpers in `Std` |
| `SplitWs`, `SplitWsFrom`, `IsSpace` | 6 | `Seq.Split` | **keep.** `Seq.Split` takes one delimiter element and keeps empty fields — Python's `s.split(' ')`. `SplitWs` collapses runs of whitespace — Python's `s.split()`. Different function |
| `ReplaceAll` | 3 | — | **keep.** No occurrences in `Std` |
| `StringLess` | 3 | `Std.Relations` | keep the predicate; its `TotalOrdering`/`SortedBy` are what `MergeSortBy` wants as a precondition |
| `PyIndex`, `DigitChar` | 3 | — | keep |
| `PrefixSum*`, `SumFrom`, `SumSeq` | 28 | `Seq.FoldLeft` | **keep.** The prelude's six `PrefixSum` lemmas are what the O(n) proofs cite; `FoldLeft` has no equivalent lemma set |
| `Opens`, `Closes`, `OnlyBrackets`, `OpensPlusCloses` | — | — | keep, problem-specific |

### The three that reverse

**`Std.Strings.ToNat` is quadratic and dies at 1000 characters.** It compiles to
genuine Python recursion on a prefix slice —
`ToNat(str[:len-1]) * base + charToDigit[c]` — one frame and one slice copy per
digit. `Prelude.ParseInt` compiles to a tail-call loop.

```
digits      ParseInt      Std.ToNat
    10        29.1us          95.7us
   100       251.9us        1240.2us
   400      1040.3us        7102.3us
   800      2095.4us       21261.0us
  1000         2.9ms    RecursionError
 64000       560.5ms    RecursionError
```

It also carries a precondition — `forall c | c in str :: IsDigitChar(c)` — that
`ParseInt` does not, so every one of the 10 call sites would need that
discharged against real inputs. `precheck.py` exists because this repo has been
bitten by preconditions that the inputs do not satisfy.

**`Seq.Max` and `Seq.Min` die at 1000 elements**, same shape: non-tail recursion
on `xs[1..]`.

```
    n     MaxSeq     Seq.Max
  500      0.80ms      1.49ms
 1000      1.53ms   RecursionError
10000     16.35ms   RecursionError
```

A contest input of 10^5 integers is routine here. This is a hard blocker, not a
performance note.

**`Prelude.IntToString` has the same bug, in `Std`'s favour.** It recurses once
per output digit and raises `RecursionError` between 900 and 1000
digits; `Std.Strings.OfInt` survives at the cost of ~7x.

```
digits   IntToString   Std.OfInt
   500        2.23ms     16.70ms
   900          ok           ok
  1000   RecursionError  39.20ms
  5000   RecursionError  37.36ms
```

317 rows call `IntToString`. **Do not swap all 317.** Find the rows whose output
integer can reach ~1000 digits — unbounded factorials, `2**n` with large n,
big-integer products with no modular reduction — and swap only those, noting the
7x in the commit message. Everywhere else the prelude version is the faster one
and the depth is unreachable.

**`Prelude.Repeat` reads like the same trap and is not one.** Its source is
`s + Repeat(s, n-1)`, but the backend turns that into an accumulator loop — no
`RecursionError` at n=2000, measured. The reason to keep it is semantic, not
cost: `Seq.Repeat(v, n)` repeats one element, `Prelude.Repeat(s, n)` repeats a
string. Where a row repeats a single character either will do.

This is why the rule below says read the emitted Python. Two functions with the
same recursive shape in `.dfy` compiled to a loop and to real recursion, and
nothing in the Dafny source says which.

### The ones that are clean

```
    n     P.Join   Seq.Join    SortInts  MergeSortBy
  100      0.75ms     0.54ms      4.47ms       4.59ms
 1000      6.04ms     6.37ms     69.83ms      68.18ms
10000         —          —      997.94ms     946.14ms
```

Equal within noise. `Seq.Join`, `Seq.Reverse`, `Seq.IndexOf`, `Seq.Repeat` and
`Seq.Flatten` all compile to tail-call loops; `Seq.MergeSortBy` recurses at depth
log n. These are the safe half of the library.

**Check before every new swap**: open the emitted `Std_*.py` and look for
`raise _dafny.TailCall()`. Its presence means a loop. Its absence in a function
that recurses on a sub-sequence means one Python frame per element, and that
function is unusable on this corpus.

## Precompiling the standard library — yes, and it buys disk, not time

`--library <file>` makes a file's contents referenceable without being generated
or verified. It works, end to end, and the measurements are:

| translate one row | wall | files | bytes |
|---|---|---|---|
| today (`include "prelude.dfy"`) | 1.06s | 6 | 60K |
| `--library prelude.doo` | 1.07s | 5 | 56K |
| `--standard-libraries` | 8.80s | 90 | 812K |
| `--library DafnyStandardLibraries.doo` | 8.33s | 6 | 60K |

Read that table twice. **Adopting `Std` costs 8x the translate time per row and
`--library` does not recover it.** The 7.5s is resolution of the library, paid
per `dafny` invocation, and a row that imports nothing from `Std` pays it too
(measured: 8.5s for a row that uses only the prelude). Across 443 rows one
validation pass goes from ~8 minutes to ~63 minutes.

What `--library` *does* buy is the emitted tree: 90 files and 812K per row
becomes 6 files and 60K. Over the corpus that is 366MB against 27MB. If `Std` is
adopted, `--library` is not optional.

### How it works

```bash
# once: generate the Std Python into a shared directory
dafny translate py --no-verify --include-runtime --standard-libraries -o std trivial.dfy
mkdir -p build/stdpy && cp std-py/Std_*.py build/stdpy/

# per row: emit only the row's own module
DOO=$(find "$HOME/.dotnet/tools/.store/dafny" -name DafnyStandardLibraries.doo | head -1)
dafny translate py --no-verify --include-runtime --allow-warnings --library "$DOO" -o out row.dfy

# run it with the shared modules importable
PYTHONPATH=build/stdpy python3 out-py/__main__.py
```

`--allow-warnings` is **required**: `--library` on a non-`.doo` emits an
`UnverifiedLibrary` warning, warnings are errors by default in `translate`, and
the failure mode is a silent exit 1 with zero files written. That zero-file
result is the warning, not a bug.

### The same trick for `prelude.dfy`, and why it is not worth it

```bash
dafny build --target lib -o prelude.doo prelude.dfy   # verifies: 57 verified, 0 errors
dafny translate py --no-verify --include-runtime --library prelude.doo -o out row_without_include.dfy
```

Clean — no warning, no `--allow-warnings`, `Prelude.py` not emitted. But it
requires **deleting `include "prelude.dfy"` from every row**: leaving the include
in while passing the `.doo` makes Dafny parse the binary as source and fail with
garbage. And the saving is 1.07s against 1.06s, i.e. nothing. Do not do this for
the prelude alone.

### It does not save verification time

`dafny verify row.dfy` reports "2 verified" with the include and "2 verified"
with `--library prelude.doo`, 1.7s either way. Dafny 4.11 does not verify
included files by default, so there was never a per-row prelude cost to remove.

### The mitigation that does work: batch the invocations

```
verify 1 file  with Std: 9.56s
verify 5 files with Std: 12.42s      (vs 47.8s as five invocations)
```

The 7.5s is per-process. If `Std` is adopted, `verify_all.py` and `proofs.py`
should pass many `.dfy` files to one `dafny` call. `translate` cannot be batched
the same way — each row needs its own output tree — so the translate cost is
real and is the number to weigh against whatever `Std` is worth.

## The work

Do it in batches, commit after each, per `CLAUDE.md` § "Checkpoint constantly".

1. **Decide the scope first, in writing.** The table above says `Sort`/`Join`/
   `Math` are safe and `ParseInt`/`MaxSeq` are not. On the measured numbers,
   adopting `Std` costs 55 extra minutes per validation pass to delete roughly
   150 lines of `prelude.dfy`. Write down whether that trade is worth taking
   before touching a row, and if it is not, say so and stop — a recorded "no"
   is a finished task.
2. If it is worth taking, wire `--library` into `validate.py`, `difftest.py`,
   `verify_all.py` and `proofs.py` **before** migrating any row, and prove the
   loop still passes on the current corpus unchanged. A migration on top of an
   unproven harness cannot be debugged.
3. Migrate one symbol at a time across all its rows — `AbsInt` first, it is the
   smallest — and run the gate for those rows only after each symbol.
4. Delete a prelude function only once **zero** rows call it. `grep -rlE
   "\bName\s*\(" solutions --include='*.dfy'` must come back empty. Keep the
   lemmas: `SortKeepsElems`, `PrefixSum*` and `JoinLen*` are cited by proofs in
   `solutions-verified/`, and those proofs are checked by `proofs.py`.
5. Re-run `verify_all.py` and `proofs.py` over `solutions-verified/`. A swap that
   changes a function's postcondition breaks proofs that `validate.py` never
   looks at.

## Rules

- **Never swap a function whose emitted Python you have not read.** `TailCall`
  present or absent is the whole decision.
- Never swap to close a gap the table marks "keep". Those are measured or
  semantic, not stylistic.
- `solutions-tofix/` is a review queue with unresolved verdicts in its headers.
  Do not migrate rows sitting there; they may be rewritten.
- Record every swap you rejected and why, in this directory. A rejected swap that
  is not written down gets re-proposed next session.
