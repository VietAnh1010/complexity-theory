---
name: bigodafny
description: Orientation and state for the BigOBench Python-to-Dafny dataset in bigodafny/. Use when resuming work on that dataset, when asked about translating rows to Dafny, verifying them, proving complexity labels, or when any of solutions/, solutions-unscreened/, solutions-disputed/, solutions-unsure/, solutions-ungateable/, solutions-unverified/, solutions-untranslated/, solutions-proved/ are involved. Read this before touching anything in bigodafny/.
---

# bigodafny — orientation

A Python→Dafny translation dataset derived from BigOBench's
`time_complexity_test_set`. 640 rows, 311 problems. Every row carries
BigOBench's inferred time-complexity label.

**Read `bigodafny/CLAUDE.md` before making changes.** It holds the rules. This
file holds the map and the reasons.

## The entry point is `bigodafny/DOCS.md`

It has the reading order and the document map; counts are in `STATUS.md`.
`bigodafny/CHANGELOG.md` dates every rule change; check a record's date against
it before reusing it. This skill is the working map; that file is the
orientation.

## Check state first, always

```bash
cd bigodafny && source .venv/bin/activate && python3 dataset.py && cat data/stats.json
for d in solutions solutions-unscreened solutions-disputed solutions-unsure \
         solutions-ungateable solutions-unverified solutions-untranslated solutions-proved; do
  printf "%-24s %s\n" "$d" "$(find $d -name '*.dfy' 2>/dev/null | wc -l)"
done
grep -rl 'TODO: translate' solutions --include='*.dfy' | wc -l   # stubs
```

The directory a row sits in *is* its classification. Never infer status from
memory or from an earlier message.

**A partition.** These seven are disjoint and cover all 640 rows; each has a
`README.md` stating what it means and how a row leaves it. Counts are in
`bigodafny/STATUS.md`.

| directory | meaning |
|---|---|
| `solutions/` | valid, `dafny verify` clean, label screened and unsuspected |
| `solutions-unscreened/` | valid; the label was never screened |
| `solutions-disputed/` | valid; the audit says the label does not match the code |
| `solutions-unsure/` | valid and verified; the label audit could not decide |
| `solutions-ungateable/` | the gate cannot reach a verdict; the stored test data fails first |
| `solutions-unverified/` | valid; safety obligations not discharged |
| `solutions-untranslated/` | will not be translated; each file states why |

**An overlay.** Not part of the partition — instrumented *copies* of rows that
also live above, so a row can exist twice with different preconditions.

| directory | meaning |
|---|---|
| `solutions-proved/` | complexity **proved** via ghost step counter |
| `solutions-proved/value-bounded/` | proved, but the bound names an input VALUE; queued for review |

Older notes use other directory names; `bigodafny/CHANGELOG.md` § Undated maps
them to these.

## The one structural fact

639 of 640 Python solutions are stdin scripts with no function signature. The
only typed argument list is `dataclass_code` — an LLM-written `Input` dataclass
BigOBench generated so its profiler could scale inputs. `signature.py` recovers
the Dafny signature from it. That field is dead weight for consuming the
benchmark and load-bearing for this dataset.

## Gates, weakest to strongest

| tool | question | applies to |
|---|---|---|
| `validate.py` | matches BigOBench's **stored** output | `strict` rows |
| `difftest.py` | matches **its own Python** | `loose` rows |
| `verify_all.py` | memory-safe for all inputs, no spec needed | everything |
| `proofs.py` | complexity **proved**; fails on any `assume`, or a proof that changes its row | `solutions-proved/`, `prelude.dfy` |
| `precheck.py` | every added `requires` holds on real inputs | anything with `requires` |
| `label_audit.py siblings` | same-problem rows converged despite different labels | everything |
| `label_audit.py` | the label describes what the code costs | `solutions/`, `solutions-disputed/` |
| `baseline.py --round-trip` | a failing strict row is the harness's fault, not the translation's | rows `validate.py` fails |

`callgraph.py` is a **measurement, not a gate**: it writes `out/call_depth.jsonl` (git-ignored),
the longest acyclic chain from `Solve` per row, ghost declarations excluded.
Use it to pick rows: depth 0–1 are self-contained and cheap to change; a deeper row pushes any
edit through helper signatures.

**Before an unproven obligation, ask whether the TRANSLATION is wrong.** Python
wraps a negative subscript; Dafny faults. Three rows read a negative index on
real inputs — they were wrong there, not merely unproven. `Prelude.PyIndex` is the fix.

`precheck.py` prints five counters. `ok` and `VIOLATED` are verdicts;
`unchecked` (Dafny could not compile the clause) and `no-data` (compiled, then
raised on every input) both mean **not checked**. `py-fails` means the clause only
excludes inputs the row's own Python also crashes on, which is a pass. Never treat
`unchecked`/`no-data` as passes.

`validate.py` is the **wrong** gate for `loose` rows: their problems accept
several correct answers, so the stored output is one of them and even the
original Python fails a byte-diff against it. Use `difftest.py` there.

## Non-negotiables

- **Audit every agent batch yourself.** Re-verify and re-validate from scratch; agents
  misreport counts and strand drafts in temp files.
- **Never accept `assume`, including `assume {:axiom}`.** The file still reports 0 errors.
  `python3 proofs.py` scans the whole corpus and exits non-zero on any hit.
- **Check every added `requires`** with `precheck.py`. A precondition narrows the
  contract until the obligation is trivial; that is the cheap way to fake a proof.
- **Never let an agent edit a gate it is judged by.**
- **A subset run never replaces a shared record** (`batches/README.md` § The `--only` trap).
- **A row's file is its status.** Move it; do not annotate and leave it.

## Running work

Batches of ~20 rows, 4 agents at a time. Larger batches do not finish before the
session limit. Agents must write directly to the `.dfy` (never a temp name) and
validate in small groups as they go, so a kill costs a group not a batch.

Sub-skills: `bigodafny-translate`, `bigodafny-verify`, `bigodafny-prove`,
`bigodafny-prove-campaign`.

## Findings that change how you work

- Not every original Python solution matches its own stored output; those
  that do are the `strict` split.
- Two defects give **correct output, wrong complexity, green tests**, and no
  gate but reading the diff catches them: doubly-recursive min/max
  (`T(n)=2T(n-1)`) and sibling reuse.
- BigOBench's tests can violate their own problems' stated limits (1501's
  private tests reach 10¹² against `k ≤ 10000`). Such tests are bogus: quote
  the limit into `data/constraints.jsonl` and the gates skip them.
- BigOBench's dataclass disagrees with what the Python reads
  (4 known cases). Read `.build/<prefix>_<SID>/dataclass.py` before assuming
  your logic is at fault.
- **`validate.py` and `difftest.py` test the row, never its proof copy.** To
  test a proof copy, use `validate.py --solutions-dir solutions-proved`; for a
  `loose` row compare the emitted Python instead.
- **`dafny verify` skips included files.** A proof reports 0 errors while a
  prelude lemma it calls does not verify. After editing the prelude, run
  `dafny verify prelude.dfy` (`proofs.py` does).
- **The cost model is stipulated, not measured** (`bigodafny/COMPLEXITY.md` § The model). A Dafny
  collection that copies where CPython assigns in place is not a defect.
- **Output costs one step per character.** `IntToString(x)` costs `Digits(x)`;
  an additive `|output|` term never counts against a label.
- **BigOBench's `O(n*m)` is wrong when the loop body does not scan a row.**
  Nine examined, seven wrong: they read `row[0]` … `row[4]` and never walk a row.
  `1855_50` is marked `O(n**2)` and is straight-line code.
