# complexity-theory

A mined dataset of **computational complexity theory** papers: harvested from
public metadata APIs, deduped, enriched, expanded along the citation graph,
exported as flat files.

Not a survey — the deliverable is `dataset/`, not prose. **No model is called
anywhere.** No API keys; stdlib Python only.

## Deliverables

| `dataset/` | |
|---|---|
| `papers.csv` | one row per paper, 25 columns |
| `papers.jsonl` | the same records, unflattened |
| `edges.csv` | `citing_id, cited_id` — citation graph induced on the library |
| `stats.json` | counts by status, subarea, venue, tier, year, source |

`edges.csv` is the *induced* subgraph — an edge only when both endpoints are in
the library — so it stays closed instead of running off into all of mathematics.

## Use

```bash
python3 scripts/run.py harvest --queries-file config/queries.txt --max 100
python3 scripts/run.py enrich                    # DOIs, venues, missing abstracts
python3 scripts/run.py snowball --seed-status included
python3 scripts/run.py dataset --edges           # the deliverable
python3 scripts/run.py verify --all              # gate; non-zero on error
```

Optional hand-labeled core tier (`SCOPE.md` § Two tiers):

```bash
python3 scripts/run.py screen next --limit 25 > batch.json
python3 scripts/run.py screen apply decisions.json
python3 scripts/run.py screen stats
```

Sources: arXiv (search + abstracts), Crossref (DOIs, venues, reference lists),
OpenCitations (citing papers). All free, keyless, unmetered — **add no keyed
source**; it fails partway through an unattended run.

Env: `SURVEY_CONTACT_EMAIL` (Crossref polite pool), `ARXIV_RATE_SECONDS`
(default 3; raise to ~10 for a long pass — see below).

## Layout

```
SCOPE.md            scope contract; screening decisions cite it
CLAUDE.md           operating rules + run procedure
STATUS.md           live run state; the handoff if a session dies
config/queries.txt  the query grid — a concept missing here is missing from the dataset
scripts/lib.py      HTTP+cache, normalization, venue table, JSONL store
scripts/topic.py    the subject: complexity vocabulary, 18 subareas
scripts/sources.py  arXiv, Crossref, OpenCitations
scripts/run.py      the CLI
papers/library.jsonl  every paper seen, deduped
dataset/            the deliverable
.cache/             raw API responses (gitignored)
```

The subject lives in `SCOPE.md`, `topic.py`, `config/queries.txt`, and the
venue table in `lib.py`. Everything else is subject-agnostic plumbing.

## Design

**No year floor.** The field's load-bearing results are decades old. Backward
snowballing from 4 seeds reached Natural Proofs (1994),
Impagliazzo–Wigderson (1997), Razborov (1987) — none of which any keyword query
surfaces.

**Enrichment is load-bearing.** Both citation sources are DOI-keyed and arXiv
supplies almost no DOIs, so the Crossref title match is what makes snowballing
possible. This field does well: 14/34 matched a published version on a smoke
test, against ~1/15 in the repo this was ported from.

**Resumable.** Responses cached by URL, library written atomically, harvest
saves every 5 queries, every command idempotent. Curated fields (status,
reason, categories, priority) survive any re-fetch.

**Fabrication is the primary risk.** This field's canonical results have names,
and a name is enough to reconstruct a citation that looks right and is wrong.
`run.py verify` re-resolves every DOI and arXiv id live and compares titles.
Tested against a planted non-existent DOI and a planted title mismatch; catches
both, exits 1.

## Traps

Each of these was a live bug, and all four hit the old foundational records
hardest — the ones snowballing exists to reach.

- **ECCC must precede CC in `VENUE_PATTERNS`.** Both contain "computational
  complexity". CC's negative lookahead only guards text *after* the match, and
  ECCC's "Colloquium" comes before, so on order alone a preprint server gets
  promoted to target tier.
- **No bare single-letter classes in `topic.py`.** `\bP\b` and `\bL\b` match
  ordinary prose in every paper ever written.
- **Crossref deposits markup inside titles** (`<i>P = BPP</i> if <i>E</i>…`),
  which breaks dedup. `lib.strip_markup` removes it; `enrich` repairs stored
  records, since upsert never overwrites a non-empty scalar.
- **Old ACM proceedings deposit an `event.name` naming no committee** ("the
  twenty-sixth annual ACM symposium") while the container spells out STOC.
  `sources._cr_venue` prefers whichever field names a venue we know.

## Known gaps

- **ECCC is not harvested** — no API, and much of this field posts there first.
  A thin subarea is not evidence of a thin literature until this is accounted for.
- **Pre-2000 records mostly lack abstracts.** Crossref has none deposited and
  there is no arXiv preprint to recover one from. They anchor the citation
  graph but cannot be screened. `stats.json` reports `with_abstract`.
- **arXiv 429s partway through a ~100-query pass** at its documented 3s floor.
  Raise `ARXIV_RATE_SECONDS` to ~10; a full grid then completes clean.
