# complexity-theory

A mined dataset of **computational complexity theory** papers, and of the
statements inside them. Harvested from public metadata APIs and arXiv LaTeX
source, deduped, enriched, exported as flat files.

Not a survey — the deliverable is `dataset/`. **No model is called anywhere.**
No API keys; stdlib Python only.

## Deliverables

The **paper layer** says which papers exist. The **statement layer** says what
is in them.

| `dataset/` | |
|---|---|
| `papers.csv` / `.jsonl` | one row per paper, 25 columns |
| `edges.csv` | `citing_id, cited_id`, induced on the library |
| `stats.json` | counts by status, subarea, venue, tier, year, source |
| `examples.csv` / `.jsonl` | one row per statement, 25 columns |
| `paper_terms.csv` | per paper: classes, problems, hypotheses used |
| `examples_stats.json` | counts by kind, subarea, class, problem, relation |
| `tasks.csv` / `.jsonl` | masked test items derived from the statements |

`edges.csv` is the *induced* subgraph — an edge only when both endpoints are in
the library — so it stays closed instead of running off into all of mathematics.

## The statement layer

A complexity paper has no dataset in the empirical sense. Its examples are
formal objects, and they sit in its theorem and definition environments. Each
statement carries:

| field | example |
|---|---|
| `kind` | theorem, lemma, definition, conjecture, open question, … |
| `classes` | canonical names, oracles merged — `ZPE^NP` is one class |
| `problems` | `Range Avoidance`, `Edit Distance`, `MCSP` — closed vocabulary |
| `named_objects` | free-form names the paper coins, so the vocabulary is not a ceiling |
| `relations` | `S2E ⊄ i.o.-SIZE[2^n/n]`, flagged `conditional` when a hypothesis governs it |
| `bounds` | `2^{n/2}`, `\Omega(n\log n)`, `SIZE[2^n/n]`, verbatim |
| `measures` | `R(f)`, `Q(f)`, `deg`, `bs` — how query and communication papers state results |
| `hypotheses` | SETH, ETH, UGC, and the rest of what a result is conditioned on |

Provenance is exact: `statement_tex` is the source byte for byte, with
`char_start`, `char_end` and `source_sha256`. `verify --examples` re-derives the
normalized source from the cached tarball and re-checks every offset. It catches
a reworded statement and a 7-character shift.

`tasks.jsonl` is the test view: one span blanked, that span as the answer, so
`prompt.replace("[MASK]", answer)` rebuilds the statement — which `verify`
checks. No true/false items: flipping `P ⊆ NP` yields an open problem, not a
falsehood, and labelling it "false" would be fabrication.

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
python3 scripts/selftest.py                      # 46 offline extractor checks, ~1s
```

`extract` fetches each paper's LaTeX source, flattens `\input`s, expands the
author's macros, and walks the theorem environments the preamble declares. It
selects round-robin across subareas, so an interrupted run is still spread
across the field. `extract --refresh --no-fetch` re-parses the cache offline —
run it after any parser change.

Hand-labeled core tier (`SCOPE.md` § Two tiers):

```bash
python3 scripts/run.py screen next --limit 25 > batch.json
python3 scripts/run.py screen apply decisions.json
```

Sources: arXiv (search, abstracts, e-print source), Crossref (DOIs, venues,
references), OpenCitations (citing papers). All free, keyless, unmetered —
**add no keyed source**; it fails partway through an unattended run.

Env: `SURVEY_CONTACT_EMAIL` (Crossref polite pool), `ARXIV_RATE_SECONDS`
(default 3, use 10 for a full grid), `ARXIV_EPRINT_SECONDS` (default 8).

## Layout

```
SCOPE.md            scope contract; screening decisions cite it
CLAUDE.md           operating rules + run procedure
STATUS.md           live run state; the handoff if a session dies
config/queries.txt  the query grid — a concept missing here is missing from the dataset
scripts/lib.py      HTTP+cache, normalization, venue table, JSONL store
scripts/topic.py    the subject: complexity vocabulary, 18 subareas
scripts/sources.py  arXiv, Crossref, OpenCitations
scripts/fulltext.py e-print source: fetch, unpack, macros, de-TeX
scripts/extract.py  statements, classes, problems, relations, bounds
scripts/run.py      the CLI
scripts/selftest.py 46 offline checks on the extractor
papers/             the stores: library, extractions, examples
dataset/            the deliverable
.cache/             raw API responses and e-print tarballs (gitignored)
```

The subject lives in `SCOPE.md`, `topic.py`, `config/queries.txt`, the venue
table in `lib.py`, and the vocabularies in `extract.py`. The rest is
subject-agnostic plumbing.

## Design

- **No year floor.** The results this field is built on are decades old, and
  only backward snowballing reaches them.
- **Enrichment is load-bearing.** Both citation sources are DOI-keyed and arXiv
  supplies almost none, so the Crossref title match is what makes snowballing work.
- **Resumable.** Responses cached by URL, stores written atomically, every
  command idempotent, `harvest` and `extract` save every 5 units.
- **Fabrication is the primary risk.** A name is enough to reconstruct a
  citation that looks right and is wrong. `verify` re-resolves every DOI and
  arXiv id live, and re-derives every statement from its cached source.

## Traps

Each was a live bug. Each was silent — the counts looked fine and the content
was wrong.

**Metadata**, all worst on the old records snowballing exists to reach:

- **ECCC must precede CC in `VENUE_PATTERNS`** — both contain "computational
  complexity", and on order alone a preprint server becomes target tier.
- **No bare single-letter classes in `topic.py`** — `\bP\b` matches prose.
- **Crossref deposits markup inside titles**, which breaks dedup.
- **Old ACM proceedings name no committee in `event.name`** while the container
  spells out STOC.

**Extraction**, all in `extract.py` and `fulltext.py`:

- **`\ensuremath` is a font wrapper.** Omit it and every class written `\cc{…}`
  is invisible; relations drop to near zero and nothing looks broken.
- **Class names are written in caps.** Fold case and the word "circuit" becomes
  the class `CIRCUIT`.
- **Longest alternative first**, or `text|mathrm|…` eats `\textnormal` and
  leaves the word "normal" in the statement.
- **`\xspace` blocks a relation match** when it sits between a class and `⊆`.
- **`\b` does not fire after `\Sigma_2`** — `_` is a word character.
- **An intersection is not its second half.** Dropping `∩ Π_2E` changes the
  claim rather than weakening it.
- **A one-letter name needs guards.** `\mathrm{e}`, `\mathbb{E}[X]`, `L^2(G)`
  and "let E be a language" are not classes.
- **A conditional is not an assertion.** "If X then P = PPAD" claims nothing
  about P and PPAD.
- **LyX writes `\newtheorem{thm}{\protect\theoremname}`** — take that as the
  printed name and the default mapping dies, dropping the whole paper.

Every one is a case in `scripts/selftest.py`. Run it after any parser change.

## Known gaps

- **ECCC is not harvested** — no API, and much of this field posts there first.
  A thin subarea is not evidence of a thin literature until this is accounted for.
- **Pre-2000 records mostly lack abstracts**, so they anchor the citation graph
  but cannot be screened.
- **No source, no statements.** PDF-only submissions and papers with no arXiv id
  contribute nothing. `extract` records `ok`/`pdf-only`/`no-tex`/`gone` per
  paper and `examples_stats.json` reports the split — reach, not just yield.
- **Statements are not numbered.** LaTeX assigns "Theorem 1.2" at typesetting
  time; `ordinal` is document position and `label` is the author's `\label`.
- **The class vocabulary is closed, the object vocabulary is not.** A class the
  paper defines itself is kept in `named_objects`, and can still appear in a
  relation when the other side is known.
- **arXiv 429s partway through a ~100-query pass** at its documented 3s floor;
  raise `ARXIV_RATE_SECONDS` to 10.
