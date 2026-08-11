# complexity-theory

A mined dataset of **computational complexity theory** papers: harvested from
public metadata APIs, deduped, enriched, expanded along the citation graph,
exported as flat files.

Not a survey — the deliverable is `dataset/`, not prose. **No model is called
anywhere.** No API keys; stdlib Python only.

## Deliverables

Two layers. The **paper layer** says which papers exist; the **statement layer**
says what is in them.

| `dataset/` | |
|---|---|
| `papers.csv` | one row per paper, 25 columns |
| `papers.jsonl` | the same records, unflattened |
| `edges.csv` | `citing_id, cited_id` — citation graph induced on the library |
| `stats.json` | counts by status, subarea, venue, tier, year, source |
| `examples.csv` | one row per extracted statement, 26 columns |
| `examples.jsonl` | the same statements, with structured relations |
| `paper_terms.csv` | per paper: which classes, problems and hypotheses it uses |
| `examples_stats.json` | counts by kind, subarea, class, problem, relation |
| `tasks.csv` / `.jsonl` | masked test items derived from the statements |

`edges.csv` is the *induced* subgraph — an edge only when both endpoints are in
the library — so it stays closed instead of running off into all of mathematics.

## The statement layer

A complexity paper has no dataset in the empirical sense. Its examples are
formal objects, and they sit in its theorem and definition environments:

- **statements** — theorem, lemma, corollary, proposition, definition, claim,
  conjecture, open question, problem, fact, observation, example;
- **problems** — `Range Avoidance`, `Edit Distance`, `MCSP`, `Set Disjointness`
  … from a closed vocabulary, plus free-form names the paper coins itself;
- **classes** — canonicalized, oracles merged (`ZPE^NP` is one class);
- **relations** — `(lhs, relation, rhs)` triples: `S2E ⊄ i.o.-SIZE[2^n/n]`;
- **bounds** — `2^{n/2}`, `\Omega(n\log n)`, `SIZE[2^n/n]`, verbatim;
- **hypotheses** — SETH, ETH, UGC, and the rest of what a result is conditioned on.

Every row carries `statement_tex` (the source, byte for byte), `char_start`,
`char_end` and `source_sha256`. `run.py verify --examples` re-derives the
normalized source from the cached tarball and checks that each statement is
still exactly at its offsets. Planting a reworded statement or shifting an
offset by seven characters both fail it.

`tasks.jsonl` is the test view: a statement with one span blanked, and that
span, verbatim, as the answer — `prompt.replace("[MASK]", answer)` must rebuild
the statement, which `verify` checks. There are no true/false items: flipping
`P ⊆ NP` to `P ⊄ NP` does not make a falsehood, it makes an open problem, and
labelling that "false" would be fabrication.

## Use

```bash
python3 scripts/run.py harvest --queries-file config/queries.txt --max 100
python3 scripts/run.py enrich                    # DOIs, venues, missing abstracts
python3 scripts/run.py snowball --seed-status included
python3 scripts/run.py dataset --edges           # the paper layer

python3 scripts/run.py extract --limit 300       # arXiv source -> statements
python3 scripts/run.py examples                  # the statement layer
python3 scripts/run.py tasks                     # masked test items
python3 scripts/run.py verify --all              # gate; non-zero on error
python3 scripts/selftest.py                      # extractor checks, offline, ~1s
```

`extract` fetches each paper's LaTeX source from arXiv, flattens `\input`s,
expands the author's own macros (`\cc{S_2E}` matches nothing until it does), and
walks the theorem environments the preamble declares. It selects round-robin
across subareas, so an interrupted run is still spread across the field, and
re-runs from cache: `extract --refresh --no-fetch` re-parses everything already
downloaded without touching the network.

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
scripts/fulltext.py arXiv e-print source: fetch, unpack, macros, de-TeX
scripts/extract.py  statements, classes, problems, relations, bounds
scripts/run.py      the CLI
scripts/selftest.py 33 offline checks on the extractor
papers/library.jsonl    every paper seen, deduped
papers/extractions.jsonl  per paper: fetch outcome, terms used
papers/examples.jsonl   every statement lifted out, with offsets
dataset/            the deliverable
.cache/             raw API responses (gitignored)
```

The subject lives in `SCOPE.md`, `topic.py`, `config/queries.txt`, the venue
table in `lib.py`, and the vocabularies in `extract.py`. Everything else is
subject-agnostic plumbing.

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

Five more from the statement layer, same story — each was live, each was silent:

- **`\ensuremath` is a font wrapper.** Leave it out of the unwrap list and every
  class written `\cc{...}` (which expands to it) is invisible; relations drop to
  near zero while the extractor still reports statements, so nothing looks broken.
- **Class names are written in caps; folding case loses that.** With
  case-insensitive matching, the word "circuit" is the class `CIRCUIT` and "size"
  is `SIZE`. `_looks_like_class` gates every match that has no font markup.
- **Longest alternative first.** `text|mathrm|...` eats `\textnormal` as `\text`
  and leaves the word "normal" sitting in the statement.
- **`\xspace` sits between a class and its relation symbol** — `NP\xspace
  \subseteq P`. Any leftover formatting command in the gap blocks the match.
- **`\b` does not fire after `\Sigma_2`.** `_` is a word character, so
  `\\Sigma\b` never matches a subscripted class; use `(?![A-Za-z])`.
- **An intersection is not its second half.** Dropping the `∩ Π_2E` from
  `Σ_2E ∩ Π_2E ⊄ SIZE[·]` does not weaken the claim, it changes it.

## Known gaps

- **ECCC is not harvested** — no API, and much of this field posts there first.
  A thin subarea is not evidence of a thin literature until this is accounted for.
- **Pre-2000 records mostly lack abstracts.** Crossref has none deposited and
  there is no arXiv preprint to recover one from. They anchor the citation
  graph but cannot be screened. `stats.json` reports `with_abstract`.
- **arXiv 429s partway through a ~100-query pass** at its documented 3s floor.
  Raise `ARXIV_RATE_SECONDS` to ~10; a full grid then completes clean.
- **No source, no statements.** PDF-only submissions and papers with no arXiv id
  contribute nothing to the statement layer. `extract` records the outcome per
  paper (`ok`, `pdf-only`, `no-tex`, `gone`) rather than dropping them, and
  `examples_stats.json` reports the split — reach, not just yield.
- **Statements are not numbered.** LaTeX assigns "Theorem 1.2" at typesetting
  time; the source does not carry it. `ordinal` is position in the document and
  `label` is the author's `\label`, where they wrote one.
- **The class vocabulary is closed, the object vocabulary is not.** A class the
  paper defines itself (`QIPL`) is not canonicalized, but it is kept in
  `named_objects` and can still appear in a relation as long as the other side
  is a known class.
