"""Export the library as a dataset.

The reference pipeline this is ported from ends in prose — an annotated
bibliography and a synthesis. This one ends here instead: flat files meant to
be loaded, joined, and measured.

    python3 scripts/dataset.py                 # papers.csv, papers.jsonl, stats.json
    python3 scripts/dataset.py --edges         # also the citation edge list (network)
    python3 scripts/dataset.py --status included   # restrict to screened-in papers

Outputs, all in dataset/:

  papers.csv     one row per paper, every field flattened to a scalar
  papers.jsonl   the same records, unflattened, for anything CSV would lose
  edges.csv      citing_id, cited_id — the induced citation graph, --edges only
  stats.json     counts by status, subarea, venue, year, and source

Nothing here calls a live API except `--edges`, so the default is instant and
re-runnable. `edges.csv` is the induced subgraph: an edge is written only when
*both* endpoints are in the library, which is what makes it a closed graph you
can compute on rather than a frontier that runs off into all of mathematics.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter

from common import DATASET_DIR, Store, log, log_event, norm_doi, venue_tier
from topic import categorize

# Column order for papers.csv. Identifiers first, then metadata, then the
# curated fields, then the text. Abstract goes last because it is the one
# column that makes a row unreadable in a terminal.
COLUMNS = [
    "id",
    "citekey",
    "doi",
    "arxiv_id",
    "title",
    "authors",
    "n_authors",
    "year",
    "venue",
    "venue_short",
    "venue_tier",
    "cited_by_count",
    "categories",
    "n_categories",
    "arxiv_categories",
    "status",
    "reason",
    "priority",
    "sources",
    "discovered_via",
    "snowball_depth",
    "first_seen",
    "url",
    "pdf_url",
    "abstract",
]

LIST_SEP = "; "


def flatten(rec: dict) -> dict:
    """One library record as a row of scalars.

    List fields are joined with "; " rather than "," so the CSV stays readable
    without quoting every cell, and so a consumer can split on a separator that
    does not occur inside author names or venue titles.
    """
    authors = rec.get("authors") or []
    cats = rec.get("categories") or categorize(rec)
    row = {
        "id": rec.get("id", ""),
        "citekey": rec.get("citekey", ""),
        "doi": rec.get("doi", ""),
        "arxiv_id": rec.get("arxiv_id", ""),
        "title": rec.get("title", ""),
        "authors": LIST_SEP.join(authors),
        "n_authors": len(authors),
        "year": rec.get("year") or "",
        "venue": rec.get("venue", ""),
        "venue_short": rec.get("venue_short", ""),
        "venue_tier": venue_tier(rec),
        "cited_by_count": rec.get("cited_by_count") or 0,
        "categories": LIST_SEP.join(cats),
        "n_categories": len(cats),
        "arxiv_categories": LIST_SEP.join(rec.get("arxiv_categories") or []),
        "status": rec.get("status", ""),
        "reason": rec.get("reason", ""),
        "priority": rec.get("priority") if rec.get("priority") is not None else "",
        "sources": LIST_SEP.join(rec.get("sources") or []),
        "discovered_via": LIST_SEP.join(rec.get("discovered_via") or []),
        "snowball_depth": rec.get("snowball_depth", 0),
        "first_seen": rec.get("first_seen", ""),
        "url": rec.get("url", ""),
        "pdf_url": rec.get("pdf_url", ""),
        "abstract": rec.get("abstract", ""),
    }
    return row


def sort_key(rec: dict):
    return (-(rec.get("year") or 0), rec.get("title", ""))


# --------------------------------------------------------------------------
# citation edges
# --------------------------------------------------------------------------

def build_edges(records: list[dict]) -> tuple[list[tuple[str, str]], dict]:
    """The citation graph induced on the library, from Crossref reference lists.

    One request per paper with a DOI, cached on disk like everything else. The
    counters returned are the honest reach of the result: papers with no DOI
    cannot be asked about, publishers that deposit references as unstructured
    text contribute nothing, and a reference to a paper outside the library is
    dropped rather than fetched.
    """
    import crossref  # imported here: the default run makes no network calls

    by_doi = {r["doi"]: r["id"] for r in records if r.get("doi")}
    edges: list[tuple[str, str]] = []
    reach = Counter()

    for rec in records:
        doi = rec.get("doi")
        if not doi:
            reach["papers_without_doi"] += 1
            continue
        try:
            refs, unstructured = crossref.reference_dois(doi)
        except Exception as exc:  # noqa: BLE001 - a paper with no deposited refs is routine
            log(f"edges: no reference list for {rec.get('citekey') or rec['id']}: {exc}")
            reach["papers_without_references"] += 1
            continue

        reach["papers_queried"] += 1
        reach["references_seen"] += len(refs) + unstructured
        reach["references_unstructured"] += unstructured
        for ref in refs:
            target = by_doi.get(norm_doi(ref))
            if target and target != rec["id"]:
                edges.append((rec["id"], target))
            elif not target:
                reach["references_outside_library"] += 1

    edges = sorted(set(edges))
    reach["edges"] = len(edges)
    return edges, dict(reach)


# --------------------------------------------------------------------------
# stats
# --------------------------------------------------------------------------

def build_stats(records: list[dict], edges_reach: dict | None) -> dict:
    cats = Counter(c for r in records for c in (r.get("categories") or categorize(r)))
    stats = {
        "papers": len(records),
        "by_status": dict(Counter(r.get("status", "candidate") for r in records)),
        "by_category": dict(cats.most_common()),
        "by_venue": dict(Counter(r.get("venue_short") or "unknown"
                                 for r in records).most_common()),
        "by_venue_tier": dict(Counter(venue_tier(r) for r in records)),
        "by_year": dict(sorted(Counter(r.get("year") or 0 for r in records).items())),
        "by_source": dict(Counter(s for r in records
                                  for s in (r.get("sources") or ["unknown"])).most_common()),
        "with_doi": sum(1 for r in records if r.get("doi")),
        "with_arxiv_id": sum(1 for r in records if r.get("arxiv_id")),
        "with_abstract": sum(1 for r in records if r.get("abstract")),
        "uncategorized": sum(1 for r in records
                             if not (r.get("categories") or categorize(r))),
    }
    if edges_reach is not None:
        stats["citation_graph"] = edges_reach
    return stats


# --------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--status", help="export only records with this status")
    ap.add_argument("--edges", action="store_true",
                    help="also build the citation graph (one Crossref request per paper)")
    args = ap.parse_args()

    store = Store()
    records = store.by_status(args.status) if args.status else list(store.records.values())
    if not records:
        log("nothing to export: the library is empty")
        return
    records.sort(key=sort_key)

    DATASET_DIR.mkdir(parents=True, exist_ok=True)

    csv_path = DATASET_DIR / "papers.csv"
    with csv_path.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=COLUMNS, extrasaction="ignore")
        writer.writeheader()
        for rec in records:
            writer.writerow(flatten(rec))

    jsonl_path = DATASET_DIR / "papers.jsonl"
    with jsonl_path.open("w", encoding="utf-8") as fh:
        for rec in records:
            fh.write(json.dumps(rec, ensure_ascii=False, sort_keys=True) + "\n")

    edges_reach = None
    if args.edges:
        edges, edges_reach = build_edges(records)
        with (DATASET_DIR / "edges.csv").open("w", encoding="utf-8", newline="") as fh:
            writer = csv.writer(fh)
            writer.writerow(["citing_id", "cited_id"])
            writer.writerows(edges)
        log(f"wrote edges.csv: {len(edges)} edges among {len(records)} papers")
        log(f"  reach: {edges_reach}")

    stats = build_stats(records, edges_reach)
    (DATASET_DIR / "stats.json").write_text(
        json.dumps(stats, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    log(f"wrote {csv_path.name}, {jsonl_path.name}, stats.json: {len(records)} papers")
    log(f"  {stats['with_abstract']} with an abstract, {stats['with_doi']} with a DOI, "
        f"{stats['uncategorized']} uncategorized")
    log_event("dataset_export", papers=len(records), status=args.status or "all",
              edges=bool(args.edges))


if __name__ == "__main__":
    main()
