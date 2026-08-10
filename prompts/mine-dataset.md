# Dataset mining run

Paste this as the prompt for an unattended session. `CLAUDE.md` and `SCOPE.md`
carry the rules; this is the procedure.

---

You are mining a dataset of computational complexity theory papers. Read
`CLAUDE.md` and `SCOPE.md` first, in full, then work through the phases below.

Two things matter more than finishing: **never invent a citation** (see the
rule in `CLAUDE.md`), and **commit after every batch** so a crash costs one
batch and not the run.

Work continuously. Do not stop to ask questions — record the question in
`STATUS.md` under "Open questions" and proceed with your best judgement.

**If the first search fails against every host, stop.** That is a network
allowlist, not the APIs. Retrying cannot fix it. Record it in `STATUS.md` and
end the session rather than burning the run on backoff.

## Phase 1 — Harvest

```bash
python3 scripts/search_arxiv.py --queries-file config/queries.txt --max 200
python3 scripts/enrich.py
python3 scripts/dataset.py
```

The grid in `config/queries.txt` carries the whole harvest — widen it now
rather than after screening. It also caps the harvest: 100 queries at `--max
200` is 20000 hits before dedup and the topic gate.

`enrich.py` is the second half of the harvest, not a tidy-up: it finds the
published DOI and venue for records that arrive as bare preprints. Two numbers
it prints belong in `STATUS.md`:

- **no abstract** — unscreenable. Mark those `unavailable`, never guess.
- **no DOI** — cannot be snowballed from. If most records land here, Phase 3
  will be thin, and that is a coverage claim you have to make honestly.

Judge the harvest by yield per query, not by the total:

- Read `logs/events.jsonl`. A query with **0 in-topic hits** is probably malformed.
- One returning far more than the rest is probably too broad.
- Add queries for what the grid misses. Use your knowledge to *choose
  queries*, never to add papers.
- Commit: `git add -A && git commit -m "harvest: N candidates"`.

## Phase 2 — Screen the core tier

`SCOPE.md` § Two tiers: the bulk of the dataset is decided automatically by
`topic.py`. This phase builds the hand-labeled subset that seeds snowballing
and measures the automatic gate's precision. **100 papers is the target, not
the whole library.**

```bash
python3 scripts/screen.py next --limit 25 > /tmp/batch.json
```

Read every abstract in the batch. Decide `included`, `excluded`, or
`unavailable` against `SCOPE.md`, then write `/tmp/decisions.json`:

```json
[
  {"id": "arxiv:2310.17762", "status": "included",
   "reason": "near-maximum circuit size lower bound for symmetric exponential time",
   "categories": ["circuit-complexity", "meta-complexity"], "priority": 3},
  {"id": "doi:10.1145/...", "status": "excluded",
   "reason": "applied — a SAT solver heuristic with no resource-bound claim"}
]
```

```bash
python3 scripts/screen.py apply /tmp/decisions.json
```

`priority` is 1–3 and drives ordering later: **3** = clearly central, **2** =
solid and in scope, **1** = borderline, included with doubt noted.

Batches are ordered target-venue-first, so if the run is cut short, what got
screened is what mattered. **Never screen a pool you have not enriched** —
straight from arXiv every record reads as venue "arXiv" with no citation count,
the sort keys all tie, and that guarantee does not hold.

Spread the core tier across subareas rather than taking the first 100 by rank.
A labeled set drawn entirely from `circuit-complexity` measures nothing about
the gate's behaviour on `descriptive-logic`.

After every batch: update `STATUS.md` with counts, then commit.

## Phase 3 — Snowball

Once ~20 papers are included:

```bash
python3 scripts/snowball.py --seed-status included --direction both
python3 scripts/enrich.py
```

This is where the dataset gets its anchors. Keyword search reaches the current
frontier; the references of what you accepted reach the results that frontier
is built on, and most of those are decades old with no arXiv presence.

Snowballed records arrive as bare DOIs, so `enrich.py` is what makes them
usable. Screen the new pool as in Phase 2, then snowball again.

Snowballing only reaches seeds with a DOI. Put the reach numbers `snowball.py`
prints into `STATUS.md`: they separate "the literature is thin here" from "our
sources are thin here", and only the first is a finding.

Stop when the criterion in `SCOPE.md` is met — two consecutive rounds each
yielding fewer than 25 new in-scope records — or the time budget runs out.
**Write down which one it was.**

## Phase 4 — Coverage

```bash
python3 scripts/dataset.py
python3 scripts/screen.py stats
```

Read `dataset/stats.json` against the targets in `SCOPE.md`:

- **A subarea under 50 papers** gets targeted queries added to
  `config/queries.txt` and a re-harvest, before anyone concludes the literature
  is thin there. Check the ECCC gap first.
- **A subarea over a quarter of the total** means its regex in `topic.py` is
  probably too loose. Read 10 of its records. If they are genuinely that
  subarea, leave it; if the regex is catching applied work, tighten it and
  re-run `dataset.py`.
- **`uncategorized` above zero** is a bug: `in_topic()` requires a subarea, so
  a record with none should not have entered the library. Investigate.

Never delete a record. `excluded` is part of the result.

## Phase 5 — Export and verify

```bash
python3 scripts/dataset.py --edges
python3 scripts/verify_citations.py --all
python3 scripts/style_check.py STATUS.md
```

**Fix every ERROR.** `verify_citations.py` errors are fabrications, broken
identifiers, or duplicate citekeys. Re-run until it exits clean, then commit.

The `--edges` run makes one Crossref request per paper with a DOI. Its reach
counters go in `STATUS.md`: `references_unstructured` is how much of the
citation graph was deposited as plain text and is invisible, and
`references_outside_library` is how much of it points outside the dataset.

## Finally

Write the closing summary in `STATUS.md`:

- counts: records, by status, by subarea, with an abstract, with a DOI
- which stopping criterion ended the run
- subareas that came out thin, and whether that is the literature, the ECCC
  gap, or the run
- the citation graph's reach numbers
- anything you were unsure about, and the calls you made
- what you would do with another eight hours

Then a final `git commit`.
