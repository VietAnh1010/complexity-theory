# Start here

You are looking at **bigodafny**: a Python → Dafny translation dataset built
from BigO(Bench)'s `time_complexity_test_set`. 640 rows, each a competitive
programming solution in Python, translated to Dafny, carrying BigOBench's
inferred time-complexity label.

The repository also contains an unrelated paper-mining pipeline at the root
(`scripts/`, `dataset/`, `papers/`). It shares nothing with this project. If
your task is about Dafny, complexity labels, or `solutions*/`, everything you
need is under `bigodafny/`.

---

## Read in this order

**If you have 10 minutes and a task to do:**

1. `bigodafny/CLAUDE.md` — the operating rules. Non-negotiable ones first.
2. This file's § *The state of the work* and § *The five rules*, below.
3. The `README.md` of whichever directory your task touches.

**If you are going to change a complexity verdict, a proof, or a charge:**

4. `bigodafny/COMPLEXITY.md` § 1 — the cost model. It is **stipulated, not
   measured**, and that changed on 2026-09-16. Anything you read elsewhere that
   says a `seq` update is O(|s|) predates it.
5. `bigodafny/batches/cost-axioms/PLAN.md` — why, and what is still unexecuted.

**If you are going to touch the corpus itself:**

6. `bigodafny/README.md` — what the dataset is and where the signature comes
   from.
7. `.claude/skills/bigodafny/SKILL.md` — the map, the gates, the findings.

**Do not read `summaries/` to learn how things work.** It is a run log, and
several of its claims were later reversed. `summaries/README.md` says which.

---

## The state of the work

| | |
|---|---|
| rows / problems | 640 / 311 |
| translated | 636 (4 cannot be — bare `print(float)`) |
| strict tier, `validate.py` | 529 valid, 3 fail |
| loose tier, `difftest.py` | 95 agree, 4 untranslatable, 1 ungateable |
| safety verified (`dafny verify`) | all 343 of `solutions/`; 333 also prove termination |
| complexity proved | 110 rows, 112 files, all verify, zero `assume` |
| label audit | 506 screened: 347 `ok`, 152 `mismatch`, 7 `unsure` (after the re-file) |
| Dafny / Z3 | 4.11.0 / 4.12.1 |

**Open, and waiting on a human decision:**

- 152 rows in `solutions-disputed/` await manual review. 118 need the *label*
  changed, 27 the *translation*, 6 both, 1 neither.
- The re-file under the cost axioms is **done** (`batches/cost-axioms/PLAN.md`
  step 3, applied by `refile.py` from a per-row decision table). 31 rows left
  the queue, 5 joined it, 3 were re-classified in place.
- One convention is unsettled across 12 rows: whether a loop bounded by the
  *value* of a capped scalar counts as constant. `solutions-disputed/README.md`
  names them.
- 127 rows in `solutions-unscreened/` have never been through the audit at all.

---

## Where a row lives

Five directories **partition** all 640 rows. A row is in exactly one, and which
one is its status. Each has a `README.md` that says what it means and how a row
leaves it.

| directory | rows | why it is not simply clean |
|---|---|---|
| `solutions/` | 343 | — it is |
| `solutions-ungateable/` | 5 | its gate cannot reach a verdict |
| `solutions-unscreened/` | 127 | its label was never screened |
| `solutions-disputed/` | 158 | the audit says the label does not match the code |
| `solutions-unverified/` | 3 | `dafny verify` cannot discharge its safety obligations |
| `solutions-untranslated/` | 4 | it will not be translated; the file says why |

`solutions-proved/` is **not** part of that partition. It holds 112 instrumented
*copies* of rows that also live above, each carrying a machine-checked
complexity bound. A row can therefore exist in two places with different
preconditions — `precheck.py`'s `find_all` exists for exactly that, and one row
(`827_148`) had two precondition sets where only the weaker was ever checked.

---

## The five rules

These are the ones that have each been broken at least once, at cost.

1. **A row is valid only if the toolchain says so.** Never mark a translation
   valid because it looks right; never hand-write an expected output.
2. **Translate the algorithm, not just the behaviour.** A row that computes the
   right answer by a different algorithm passes every test and corrupts the
   label, which is the dataset's whole point. Restructuring *within* a
   complexity class is fine; replacing the algorithm is not.
3. **Neither gate may be edited by an agent whose work it judges.** One agent
   cut difftest's Python budget while fixing a real bug in the same edit; the
   fix was kept, the cut reverted.
4. **A tool that takes a subset and writes a shared file will clobber it.**
   Four did, and one of them hid an ungateable row for months by keeping
   `data/difftest.jsonl` at 5 rows for a tier of 100. `batches/README.md`
   § *The `--only` trap* lists all four and their fixes. Assume a new one has
   this bug until you have checked.
5. **Failures are data.** An unmappable signature, an ungateable row, a
   rejected batch — each is recorded with its reason, never dropped silently.

---

## The gates, weakest to strongest

| tool | question | applies to |
|---|---|---|
| `validate.py` | matches BigOBench's **stored** output | 534 `strict` rows |
| `difftest.py --loose` | matches **its own Python** | 100 `loose` rows |
| `verify_all.py` | memory-safe for all inputs, no spec needed | everything |
| `precheck.py SID...` | every added `requires` holds on real inputs | anything with `requires` |
| `proofs.py` | complexity **proved**; fails on any `assume` | `solutions-proved/` |
| `labelaudit.py` + `checkverdicts.py` | the label describes what the code costs | `solutions/` |
| `siblings.py` | two rows of one problem converged despite different labels | everything |

`validate.py` is the **wrong** gate for loose rows — their problems accept
several correct answers, so even the original Python fails a byte-diff against
the stored output.

`refile.py` re-files audited rows after a change to the cost model. It is not a
re-audit: every move is derived from what a recorded verdict already says, and
the derivation is written per row in `batches/cost-axioms/refile_decisions.jsonl`.
Re-running it is safe — a row already moved has only its record rewritten.

`callgraph.py` is a measurement, not a gate: longest acyclic chain from `Solve`
per row, in `data/call_depth.jsonl`. Depth 0–1 rows are self-contained and cheap
to change.

`cli.py` covers only the deterministic build (extract → signatures → scaffold →
baseline → validate → dataset). Everything above is run directly, because each
takes a judgement as input or produces one as output.

---

## The document map

**Current — these describe how things are now.**

| file | what it is |
|---|---|
| `DOCS.md` | this file |
| `CLAUDE.md` | operating rules; read before changing anything |
| `README.md` | what the dataset is, where the signature comes from, status |
| `COMPLEXITY.md` | the cost model (§ 1) and the proof technique (§ 2) |
| `solutions*/README.md` | one per tier: what it means, how a row leaves |
| `batches/README.md` | what each campaign was; the `--only` trap |
| `summaries/README.md` | index of the run log, and which claims were reversed |
| `experiments/README.md` | the blind-vs-labeled proving experiment |
| `LICENSE.md` | CC-BY-NC-4.0, inherited from BigOBench |

**Instructions — written to be handed to an agent.**

| file | status |
|---|---|
| `batches/labelaudit/PROMPT.md` | current; its cost table was rewritten with the axioms |
| `batches/cost-axioms/PLAN.md` | steps 1, 2 and 4 done; **step 3 not run** |
| `batches/stdlib-migration/PROMPT.md` | researched, never run — moving `prelude.dfy` call sites to `Std` |
| `.claude/skills/bigodafny*/SKILL.md` | four skills: orientation, translate, verify, prove |

**Historical — a record, not documentation. Do not act on these.**

| path | why it is kept |
|---|---|
| `summaries/*.md` | 16 wave and sweep write-ups. Several claims were later reversed; the index says which. |
| `experiments/runs/pilot1/guide_archive/GUIDE.v1–v4.md` | which guide each blind-arm agent was shown. Deleting them would destroy the experiment's provenance. |
| `batches/labelaudit/verdicts_19.rejected.jsonl` | a batch the schema gate refused |

---

## The one thing most likely to mislead you

**The cost model changed.** Until 2026-09-16 every charge in this project was
read off Dafny's Python backend, where `s[i := v]` copies the whole sequence and
a loop CPython runs in O(n) runs in O(n²). That produced the largest "defect"
class in the project — 93 rows.

It is gone. The charges are now stipulated: `s[i := v]`, `m[k := v]` and set
insertion are all `1`, independent of backend. The reason is that BigOBench's
labels were measured on **CPython**, so a model derived from Dafny's Python
backend was comparing two unrelated implementations and calling the difference a
translation defect.

Three consequences you will trip over:

- **Old verdicts used the old table.** All 25 `batches/labelaudit/verdicts_*.jsonl`
  files, and every header in `solutions-disputed/`, were filed against it. Do not
  compare a verdict across the boundary without checking which model it used.
- **Old proofs were re-checked, and the overcharge claim was wrong.** All 33
  files in `solutions-proved/` predate the switch; all 33 still verify under
  it and none needed re-proving. No proof performs a `seq` update, so the
  retired charge reaches none of them. `COMPLEXITY.md` § 1 records the check.
- **The axioms are false of the artifact.** A row charged O(n) can take O(n²) of
  wall-clock. `COMPLEXITY.md`'s appendix records where, and two rows in
  `solutions/` keep an `array<T>` because of it — they are the corpus's only
  arrays, and each says so in a header comment.

---

## Running anything

```bash
export PATH="$PATH:$HOME/.dotnet/tools"          # dafny lives here
python3 dataset.py                               # rebuild data/dataset.jsonl + stats.json
python3 validate.py --only 1053_38               # spot-check one strict row
python3 difftest.py --loose                      # the whole loose tier (~30 min)
python3 proofs.py                                # re-verify all 33 proofs
dafny verify --solver-path /usr/local/bin/z3 solutions/1053/1053_38.dfy
```

`data/tasks.jsonl` (76 MB), `.cache/` and `.build/` are gitignored and
regenerable. `.build/` grows to hundreds of MB; clear it when disk is short.

**The directory a row sits in is its status, never an earlier message.** Check
state before trusting a handoff, including this one.
