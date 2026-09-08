---
name: bigodafny
description: Orientation and state for the BigOBench Python-to-Dafny dataset in bigodafny/. Use when resuming work on that dataset, when asked about translating rows to Dafny, verifying them, proving complexity labels, or when any of solutions/, solutions-unverified/, solutions-inexact/, solutions-untranslated/, solutions-verified/ are involved. Read this before touching anything in bigodafny/.
---

# bigodafny — orientation

A Python→Dafny translation dataset derived from BigOBench's
`time_complexity_test_set`. 640 rows, 311 problems. Every row carries
BigOBench's inferred time-complexity label.

**Read `bigodafny/CLAUDE.md` before making changes.** It holds the rules. This
file holds the map and the reasons.

## Check state first, always

```bash
cd bigodafny && python3 dataset.py && cat data/stats.json
for d in solutions solutions-unverified solutions-inexact solutions-untranslated; do
  printf "%-24s %s\n" "$d" "$(find $d -name '*.dfy' 2>/dev/null | wc -l)"
done
grep -rl 'TODO: translate' solutions --include='*.dfy' | wc -l   # stubs
```

The directory a row sits in *is* its classification. Never infer status from
memory or from an earlier message.

| directory | meaning |
|---|---|
| `solutions/` | valid, `dafny verify` clean, complexity label unsuspected |
| `solutions-unverified/` | valid; safety obligations not discharged |
| `solutions-inexact/` | complexity label suspect (sibling reuse or `set<T>`) |
| `solutions-untranslated/` | will not be translated; each file states why |
| `solutions-verified/` | complexity **proved** via ghost step counter |
| `solutions-nlogn/` | two sort rows at the tight O(n log n) bound |

## The one structural fact

639 of 640 Python solutions are stdin scripts with no function signature. The
only typed argument list is `dataclass_code` — an LLM-written `Input` dataclass
BigOBench generated so its profiler could scale inputs. `signature.py` recovers
the Dafny signature from it. That field is dead weight for consuming the
benchmark and load-bearing for this dataset.

## Gates, weakest to strongest

| tool | question | applies to |
|---|---|---|
| `validate.py` | matches BigOBench's **stored** output | 534 `strict` rows |
| `difftest.py` | matches **its own Python** | 100 `loose` rows |
| `verify_all.py` | memory-safe for all inputs, no spec needed | everything |
| `proofs.py` | complexity **proved**; fails on any `assume` | `solutions-verified/` |
| `precheck.py` | every added `requires` holds on real inputs | anything with `requires` |
| `siblings.py` | same-problem rows converged despite different labels | everything |

`precheck.py` prints four counters. `ok` and `VIOLATED` are verdicts;
`unchecked` (shape did not translate) and `no-data` (translated, then raised on
every input) both mean **not checked**. Treating them as passes is how a gate
stops gating — it happened, and hid four real violations.

`validate.py` is the **wrong** gate for `loose` rows: their problems accept
several correct answers, so the stored output is one of them and even the
original Python fails a byte-diff against it. Use `difftest.py` there.

## Non-negotiables

- **Audit every agent batch yourself.** Re-verify and re-validate from scratch.
  This has caught a 19/20 reported that was 18/20, a batch reported as 0/20 that
  had 20 drafts stranded in `.new` files, and an agent editing the gate.
- **Never accept `assume`.** It silences an obligation rather than discharging
  it. Unverified is strictly better than a hollow proof.
- **Check every added `requires`** with `precheck.py`. A precondition narrows the
  contract until the obligation is trivial; that is the cheap way to fake a proof.
- **Never let an agent edit a gate it is judged by.** One cut difftest's
  reference-Python budget from 30s to 10s inside an otherwise-real fix; slow rows
  would have dropped out of the comparison, passing more rows by checking fewer.
- **A row's file is its status.** Move it; do not annotate and leave it.

## Running work

Batches of ~20 rows, 4 agents at a time. Larger batches do not finish before the
session limit. Agents must write directly to the `.dfy` (never a temp name) and
validate in small groups as they go, so a kill costs a group not a batch.

Sub-skills: `bigodafny-translate`, `bigodafny-verify`, `bigodafny-prove`.

## Findings that change how you work

- Only **540/640** original Python solutions match their own stored output.
  That is the ceiling for byte-diff.
- Three defects give **correct output, wrong complexity, green tests**, and no
  gate but reading the diff catches them: doubly-recursive min/max
  (`T(n)=2T(n-1)`), sibling reuse, and `set<T>` built in a loop (measured
  O(n²) in Dafny's Python backend).
- Two O(n·m) labels were **proved wrong** — the `m` named nothing that varies.
- BigOBench's generated tests violate their own problems' stated constraints
  (3 known cases), and its dataclass disagrees with what the Python reads
  (4 known cases). Read `.build/<prefix>_<SID>/dataclass.py` before assuming
  your logic is at fault.
- Asking for verification **while translating** gets 97.5%; retrofitting later
  also reached 97.5%, but only after the rows were written.
- **A gate with a bug is worse than no gate**, because it reports success.
  `precheck.py` had four: it swallowed `//` comments into the clause, rewrote
  char literals like `'A'` into field lookups (producing false VIOLATIONs), hid
  its own `no-data` count, and could not translate `exists`, element
  quantifiers, or the prelude helpers. 29 of 444 clauses were passing without
  ever being evaluated, and six genuinely bad preconditions were invisible.
- `Sort` now carries permutation lemmas (`SortKeepsElems` and friends). Before
  that, every fact about a sequence's contents was lost across a sort and rows
  hand-wrote the same lemma over and over.
