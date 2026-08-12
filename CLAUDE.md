# Operating rules

Mines a dataset of computational complexity theory papers. Read `SCOPE.md`
before any screening decision.

## The one rule that matters

**Never write a paper, title, author, venue, year, DOI, number, theorem
statement, or quotation from memory.** Every fact here must come from a response
fetched this session. A statement in `papers/examples.jsonl` is a byte-exact
slice of a fetched LaTeX source or it does not belong there.

You know this literature. That knowledge is for *choosing queries* and *judging
results* — never for filling a field. A name is enough to reconstruct a citation
that looks right and is wrong, and a plausible citation is worse than a missing
one because it is invisible. If a lookup fails, set `unavailable` and move on.

`run.py verify` re-resolves DOIs and arXiv ids live, and re-derives every
statement from its source. Run it before declaring anything finished.

## No model is in this pipeline

Sources are arXiv, Crossref, OpenCitations — free, keyless, unmetered. No
script calls a language model and none should. The only judgement an agent
makes is core-tier screening, from a fetched abstract against `SCOPE.md`.

## Rules

- **Screen in bulk.** `screen next` emits a batch, `screen apply` writes back.
  Never one subprocess per paper.
- **Screen from the abstract, not the title.** No abstract → run `enrich`;
  still none → `unavailable`, never a guess.
- **`signals` is a prior, not a verdict.** Keyword match; good papers trip it.
- **Checkpoint constantly.** Every batch: update `STATUS.md`, then commit.
- **Record why.** Every include and exclude carries a `reason`.
- **Failures are data.** Unfetchable → `unavailable`, with the reason. Never
  drop silently, never fill from memory.
- **Report reach, not just yield.** Seeds without a DOI, references deposited
  unstructured, papers OpenCitations has no data for. Those numbers separate
  "the literature is thin here" from "our sources are thin here". Only the
  first is a finding.

`enrich` is not optional — both citation sources are DOI-keyed and arXiv
supplies almost none. Run it after every harvest and every snowball round.

## Run procedure

**Work continuously.** Don't stop to ask; record the question in `STATUS.md`
under Open questions and proceed on best judgement. If the first search fails
against every host, that is a network allowlist, not the APIs — record it and
stop rather than burning the run on backoff.

**1. Harvest.** `run.py harvest --queries-file config/queries.txt --max 100`,
then `run.py enrich`. Use `ARXIV_RATE_SECONDS=10` for a full grid. The grid
carries the whole harvest — widen it now, not after screening. Read
`logs/events.jsonl`: a query with 0 hits is malformed; one returning far more
than the rest is too broad. Two `enrich` numbers go in `STATUS.md` — records
with no abstract (unscreenable) and no DOI (unsnowballable).

**2. Screen the core tier.** Target ~100 papers, not the whole library —
`SCOPE.md` § Two tiers. Batches are target-venue-first, so an interrupted run
screened what mattered. **Never screen an unenriched pool**: straight from
arXiv every record reads venue "arXiv" with no citation count, the sort keys
tie, and that guarantee fails. Spread across subareas; a labeled set drawn
entirely from `circuit-complexity` measures nothing about the gate elsewhere.

```json
[{"id": "arxiv:2310.17762", "status": "included", "priority": 3,
  "reason": "near-maximum circuit size lower bound for symmetric exponential time",
  "categories": ["circuit-complexity", "meta-complexity"]},
 {"id": "doi:10.1145/...", "status": "excluded",
  "reason": "applied — SAT solver heuristic, no resource-bound claim"}]
```

`priority`: 3 = clearly central, 2 = solid, 1 = borderline, doubt in `reason`.

**3. Snowball.** At ~20 included: `run.py snowball --seed-status included`,
then `enrich`. This is where the dataset gets its anchors — keyword search
reaches the frontier; references reach what the frontier is built on. Screen
the new pool, repeat. Stop per `SCOPE.md`, and **write down which criterion**.

**4. Coverage.** `run.py dataset` then read `dataset/stats.json` against
`SCOPE.md` targets. A subarea under 50 gets targeted queries first — check the
ECCC gap before calling a literature thin. A subarea over a quarter of the
total means its regex is too loose; read 10 of its records. `uncategorized`
above zero is a bug: `in_topic` requires a subarea. Never delete a record.

**5. Extract the statements.** `run.py extract --limit N`, then `run.py
examples` and `run.py tasks`. Selection is round-robin across subareas, so an
interrupted run is still spread across the field; `--no-spread` for rank order.

- **Read the output.** Sample 15 statements after any parser change. Every
  defect found so far was invisible in the counts and obvious in the text.
- **`python3 scripts/selftest.py` after any parser change.** Offline, one
  second, and every case in it was a live bug.
- **Re-parse the whole store, not just new papers.** `extract --refresh
  --no-fetch` re-runs the parser over the cache with no network.
- **Fetch outcomes are data.** Report the `pdf-only`/`no-tex`/`gone` split; it
  is the reach of this layer.
- **The vocabularies in `extract.py` are patterns, not facts.** Add names the
  papers show you. Never add a claim.

**6. Export and verify.** `run.py dataset --edges` then `run.py verify --all`.
Fix every ERROR; re-run until clean. `verify` re-derives every statement from
its cached source byte for byte, and every test item from its statement. The
`--edges` reach counters go in `STATUS.md`.

**Finally**, in `STATUS.md`: counts, which stopping criterion ended the run,
thin subareas and whether that is the literature or the ECCC gap, the graph's
reach numbers, the statement layer's fetch-outcome split, calls made under
uncertainty, what another eight hours would do.

## Style

`.claude/skills/my-concise/SKILL.md` governs `STATUS.md` and anything said to
the user: bullets, one claim each, ~100 characters, no hedges. This repo
produces no prose deliverable — keep that surface small. A claim written down
is a claim someone has to check.
