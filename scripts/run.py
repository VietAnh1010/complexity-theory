"""One CLI for the pipeline. Every subcommand is idempotent and resumable.

    run.py harvest  --queries-file config/queries.txt --max 100
    run.py enrich
    run.py screen next --limit 25 | run.py screen apply decisions.json | run.py screen stats
    run.py snowball --seed-status included
    run.py dataset --edges
    run.py verify --all
"""
from __future__ import annotations
import argparse, csv, json, random, re, sys, time
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict

import extract as EX
import fulltext as FT
import sources as S
from lib import (DATA, ROOT, STATUSES, Store, citekeys, event, get, getj, load_jsonl,
                 log, ndoi, real_venue, save_jsonl, strip_markup, tier, tsim, venue)
from topic import categorize, in_topic, prior

SAVE_EVERY = 5  # a ~100-query pass gets 429'd partway through; don't lose the rest


# ---- harvest -------------------------------------------------------------
def harvest(a):
    st, new, kept = Store(), 0, 0
    qs = list(a.query)
    if a.queries_file:
        qs += [l.split("#")[0].strip() for l in open(a.queries_file, encoding="utf-8")
               if l.split("#")[0].strip()]
    if not qs: sys.exit("give --query or --queries-file")
    cats = [c.strip() for c in a.categories.split(",") if c.strip()]
    for i, q in enumerate(qs, 1):
        try:
            es = S.ax_search(q, cats, a.max)
        except Exception as e:
            log(f"query failed: {q!r}: {e}"); event("query_failed", query=q, error=str(e)); continue
        n = k = skip = 0
        for e in es:
            r = S.ax_parse(e, f"arxiv:{q}")
            if r is None: continue
            if (r.get("year") and r["year"] < a.from_year) or (not a.no_topic_gate and not in_topic(r)):
                skip += 1; continue
            _, isnew = st.upsert(r); n += isnew; k += 1
        new, kept = new + n, kept + k
        log(f"{q!r}: {len(es)} hits, {k} kept, {n} new, {skip} filtered")
        event("query", query=q, hits=len(es), kept=k, new=n, skipped=skip)
        if i % SAVE_EVERY == 0: st.save()
    st.save()
    log(f"done: {new} new / {kept} kept; library {len(st.recs)}: {st.counts()}")


# ---- enrich --------------------------------------------------------------
def bad_venue(r):
    """Venue stored but matching nothing. Retried each run; the response is cached."""
    return bool(r.get("doi")) and real_venue(r) and not venue(r.get("venue"))


def enrich(a):
    st = Store()
    pool = st.by_status(a.status) if a.status else list(st.recs.values())
    tg = [r for r in pool if not r.get("abstract") or not real_venue(r) or not r.get("doi") or bad_venue(r)]
    log(f"{len(tg)} of {len(pool)} missing an abstract, venue, or DOI")

    by_doi = {r["doi"]: r for r in tg if r.get("doi")}
    filled = 0
    for f in S.cr_by_dois(list(by_doi), "enrich:crossref") if by_doi else []:
        r = by_doi.get(f.get("doi", ""))
        if r is None: continue
        before = (r.get("abstract"), r.get("venue"))
        if not r.get("abstract") and f.get("abstract"): r["abstract"] = f["abstract"]
        # Only overwrite of a non-empty field, and it never loses information:
        # a venue string matching nothing is replaced by one that matches.
        if f.get("venue") and (not real_venue(r) or (bad_venue(r) and venue(f["venue"]))):
            r["venue"], r["venue_short"] = f["venue"], f.get("venue_short") or venue(f["venue"])
        for k in ("authors", "year", "url", "pdf_url", "cited_by_count"):
            if not r.get(k) and f.get(k): r[k] = f[k]
        filled += (r.get("abstract"), r.get("venue")) != before

    matched = 0
    if not a.skip_title_match:
        pend = [r for r in tg if not r.get("doi") and r.get("title")]
        log(f"crossref: title-matching {len(pend)} with no DOI")
        for r in pend:
            p = S.cr_by_title(r["title"], "enrich:crossref-title")
            if not p or not p.get("doi") or st.find({"doi": p["doi"]}): continue
            r["doi"] = p["doi"]
            if p.get("venue"): r["venue"], r["venue_short"] = p["venue"], p.get("venue_short") or venue(p["venue"])
            if not r.get("abstract") and p.get("abstract"): r["abstract"] = p["abstract"]
            r["sources"] = list(dict.fromkeys(r.get("sources", []) + ["crossref"])); st.index(r); matched += 1

    recovered = 0
    if not a.skip_arxiv:
        pend = [r for r in tg if not r.get("abstract") and r.get("title")]
        log(f"arxiv: title-matching {len(pend)} with no abstract")
        for r in pend:
            m = S.ax_by_title(r["title"])
            if not m: continue
            r["abstract"] = m["abstract"]
            for k in ("arxiv_id", "pdf_url"):
                if not r.get(k) and m.get(k): r[k] = m[k]
            r["sources"] = list(dict.fromkeys(r.get("sources", []) + ["arxiv"])); recovered += 1

    revised = retitled = 0
    for r in st.recs.values():
        if (d := venue(r.get("venue"))) and d != r.get("venue_short", ""): r["venue_short"] = d; revised += 1
        # upsert never overwrites a non-empty scalar, so markup stripped after
        # the record landed must be repaired in place.
        if (c := strip_markup(r.get("title"))) and c != r.get("title"): r["title"] = c; st.index(r); retitled += 1
    st.save()

    na = sum(1 for r in pool if not r.get("abstract"))
    nd = sum(1 for r in pool if not r.get("doi"))
    log(f"crossref {filled}, {matched} published versions, arxiv {recovered}, "
        f"{revised} venues revised, {retitled} titles cleaned")
    log(f"{na} still unscreenable (no abstract); {nd} cannot be snowballed from (no DOI)")
    event("enrich", crossref=filled, published=matched, arxiv=recovered, no_abstract=na, no_doi=nd)


# ---- screen --------------------------------------------------------------
def screen(a):
    st = Store()
    if a.action == "next":
        pool = st.by_status("candidate")
        if a.venue_tier: pool = [r for r in pool if tier(r) == a.venue_tier]
        if a.category: pool = [r for r in pool if a.category in categorize(r)]
        # Target venues first, so an interrupted run screened what mattered.
        pool.sort(key=lambda r: ({"target": 0, "other": 1, "unknown": 2}[tier(r)],
                                 -(r.get("cited_by_count") or 0), -(r.get("year") or 0)))
        json.dump({"remaining": len(pool), "batch": [{
            "id": r["id"], "citekey": r.get("citekey", ""), "title": r.get("title", ""),
            "authors": (r.get("authors") or [])[:6], "year": r.get("year"),
            "venue": r.get("venue", ""), "venue_short": r.get("venue_short", ""), "venue_tier": tier(r),
            "cited_by_count": r.get("cited_by_count", 0), "abstract": r.get("abstract", ""),
            "url": r.get("url") or r.get("pdf_url", ""), "discovered_via": r.get("discovered_via", []),
            "signals": prior(r)} for r in pool[:a.limit]]}, sys.stdout, ensure_ascii=False, indent=2)
        print(); return

    raw = open(a.file, encoding="utf-8").read().strip()
    ds = (json.loads(raw) if raw.startswith("[") else
          json.loads(raw)["decisions"] if raw.startswith("{") and '"decisions"' in raw[:200] else
          [json.loads(l) for l in raw.splitlines() if l.strip()])
    bad = []
    for d in ds:
        ident = d.get("id") or d.get("citekey")
        r = st.recs.get(ident) or next((x for x in st.recs.values() if x.get("citekey") == ident), None) \
            or st.recs.get(st._ax.get(ident, ""))
        if r is None: bad.append(f"UNKNOWN {ident}"); continue
        if d.get("status") not in STATUSES: bad.append(f"BAD-STATUS {ident}"); continue
        r.update(status=d["status"], reason=d.get("reason", "").strip(),
                 screened_at=time.strftime("%Y-%m-%d"), categories=d.get("categories") or categorize(r))
        if d.get("priority") is not None: r["priority"] = int(d["priority"])
        if d.get("tags"): r["tags"] = d["tags"]
    citekeys(st); st.save()
    log(f"applied {len(ds)-len(bad)}/{len(ds)}; library {st.counts()}")
    for b in bad: log(f"  !! {b}")
    event("screen_apply", applied=len(ds) - len(bad), failed=len(bad))
    if bad: sys.exit(1)


def stats(a):
    st = Store(); inc = st.by_status("included")
    print(f"library: {len(st.recs)} records")
    for s, n in st.counts().items(): print(f"  {s:12} {n}")
    print(f"\nvenue tier (all): {dict(Counter(tier(r) for r in st.recs.values()))}")
    print(f"\nincluded by category ({len(inc)}):")
    for c, n in Counter(c for r in inc for c in (r.get("categories") or categorize(r))).most_common():
        print(f"  {c:26} {n}")


# ---- snowball ------------------------------------------------------------
def absorb(st, recs, from_year, gate):
    new = skip = 0
    for r in recs:
        if (r.get("year") and r["year"] < from_year) or (gate and not in_topic(r)): skip += 1; continue
        r["snowball_depth"] = 1
        _, isnew = st.upsert(r); new += isnew
    return new, skip


def snowball(a):
    st = Store(); seeds = st.by_status(a.seed_status)
    if not seeds: return log(f"no records with status={a.seed_status!r}")
    gate, added = not a.no_topic_gate, 0
    nodoi = sum(1 for s in seeds if not s.get("doi"))
    if nodoi: log(f"{nodoi}/{len(seeds)} seeds have no DOI and cannot be expanded")
    known = {r["doi"] for r in st.recs.values() if r.get("doi")}
    karx = {r["arxiv_id"] for r in st.recs.values() if r.get("arxiv_id")}

    if a.direction in ("backward", "both"):
        want, withdoi, unstruct = {}, 0, 0
        for s in seeds:
            if not s.get("doi"): continue
            withdoi += 1; lbl = s.get("citekey") or s["id"]
            try: refs, u = S.cr_refs(s["doi"])
            except Exception as e: log(f"backward: no refs for {lbl}: {e}"); continue
            unstruct += u
            for d in refs:
                if d not in known: want.setdefault(d, lbl)
        log(f"backward: {len(want)} unseen refs across {withdoi} seeds with a DOI; "
            f"{unstruct} refs had no DOI")
        if want:
            fetched = S.cr_by_dois(list(want), "snowball:backward")
            for r in fetched:
                if (l := want.get(r.get("doi", ""))): r["discovered_via"] = [f"snowball:backward:{l}"]
            n, sk = absorb(st, fetched, a.from_year, gate); added += n
            log(f"backward: {len(fetched)} resolved, {n} new, {sk} filtered")
            event("snowball_leg", direction="backward", new=n, unstructured_refs=unstruct)

    if a.direction in ("forward", "both"):
        n = sk = 0
        for s in seeds:
            if not s.get("doi"): continue
            lbl = s.get("citekey") or s["id"]
            try: edges = S.oc_citing(s["doi"])
            except Exception as e: log(f"forward failed for {lbl}: {e}"); continue
            win = sorted([e for e in edges if not e["year"] or e["year"] >= a.from_year],
                         key=lambda e: e["year"] or 0, reverse=True)[:a.max_forward]
            f = S.cr_by_dois([e["doi"] for e in win if e["doi"] and e["doi"] not in known],
                             f"snowball:forward:{lbl}")
            f += S.ax_by_ids([e["arxiv_id"] for e in win if e["arxiv_id"] and not e["doi"]
                              and e["arxiv_id"] not in karx], f"snowball:forward:{lbl}")
            a_, b_ = absorb(st, f, a.from_year, gate); n += a_; sk += b_
            log(f"forward: {lbl} cited by {len(edges)} ({len(win)} in window), {len(f)} resolved, {a_} new")
        added += n; log(f"forward: {n} new, {sk} filtered")
        event("snowball_leg", direction="forward", new=n)

    st.save(); log(f"snowball added {added}; library {len(st.recs)}: {st.counts()}")


# ---- dataset -------------------------------------------------------------
COLS = ["id", "citekey", "doi", "arxiv_id", "title", "authors", "n_authors", "year", "venue",
        "venue_short", "venue_tier", "cited_by_count", "categories", "n_categories",
        "arxiv_categories", "status", "reason", "priority", "sources", "discovered_via",
        "snowball_depth", "first_seen", "url", "pdf_url", "abstract"]
SEP = "; "  # not "," — it never occurs inside an author name or venue title


def dataset(a):
    st = Store()
    recs = st.by_status(a.status) if a.status else list(st.recs.values())
    if not recs: return log("library is empty")
    recs.sort(key=lambda r: (-(r.get("year") or 0), r.get("title", "")))
    DATA.mkdir(parents=True, exist_ok=True)

    def row(r):
        au, cats = r.get("authors") or [], r.get("categories") or categorize(r)
        return {**{k: r.get(k, "") for k in
                   ("id", "citekey", "doi", "arxiv_id", "title", "venue", "venue_short",
                    "status", "reason", "first_seen", "url", "pdf_url", "abstract")},
                "authors": SEP.join(au), "n_authors": len(au), "year": r.get("year") or "",
                "venue_tier": tier(r), "cited_by_count": r.get("cited_by_count") or 0,
                "categories": SEP.join(cats), "n_categories": len(cats),
                "arxiv_categories": SEP.join(r.get("arxiv_categories") or []),
                "priority": r.get("priority") if r.get("priority") is not None else "",
                "sources": SEP.join(r.get("sources") or []),
                "discovered_via": SEP.join(r.get("discovered_via") or []),
                "snowball_depth": r.get("snowball_depth", 0)}

    with (DATA / "papers.csv").open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=COLS, extrasaction="ignore", lineterminator="\n")
        w.writeheader(); [w.writerow(row(r)) for r in recs]
    with (DATA / "papers.jsonl").open("w", encoding="utf-8") as fh:
        for r in recs: fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")

    reach = None
    if a.edges:
        # Induced subgraph: an edge only when both endpoints are in the library,
        # which keeps it closed rather than a frontier into all of mathematics.
        by_doi = {r["doi"]: r["id"] for r in recs if r.get("doi")}
        edges, reach = [], Counter()
        for r in recs:
            if not r.get("doi"): reach["papers_without_doi"] += 1; continue
            try: refs, u = S.cr_refs(r["doi"])
            except Exception as e:
                log(f"edges: no refs for {r.get('citekey') or r['id']}: {e}")
                reach["papers_without_references"] += 1; continue
            reach["papers_queried"] += 1; reach["references_seen"] += len(refs) + u
            reach["references_unstructured"] += u
            for d in refs:
                t = by_doi.get(ndoi(d))
                if t and t != r["id"]: edges.append((r["id"], t))
                elif not t: reach["references_outside_library"] += 1
        edges = sorted(set(edges)); reach["edges"] = len(edges); reach = dict(reach)
        with (DATA / "edges.csv").open("w", encoding="utf-8", newline="") as fh:
            w = csv.writer(fh, lineterminator="\n"); w.writerow(["citing_id", "cited_id"]); w.writerows(edges)
        log(f"edges.csv: {len(edges)} edges; reach: {reach}")

    cats = Counter(c for r in recs for c in (r.get("categories") or categorize(r)))
    stat = {"papers": len(recs),
            "by_status": dict(Counter(r.get("status", "candidate") for r in recs)),
            "by_category": dict(cats.most_common()),
            "by_venue": dict(Counter(r.get("venue_short") or "unknown" for r in recs).most_common()),
            "by_venue_tier": dict(Counter(tier(r) for r in recs)),
            "by_year": dict(sorted(Counter(r.get("year") or 0 for r in recs).items())),
            "by_source": dict(Counter(s for r in recs for s in (r.get("sources") or ["unknown"])).most_common()),
            "with_doi": sum(1 for r in recs if r.get("doi")),
            "with_arxiv_id": sum(1 for r in recs if r.get("arxiv_id")),
            "with_abstract": sum(1 for r in recs if r.get("abstract")),
            "uncategorized": sum(1 for r in recs if not (r.get("categories") or categorize(r)))}
    if reach: stat["citation_graph"] = reach
    (DATA / "stats.json").write_text(json.dumps(stat, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    log(f"{len(recs)} papers; {stat['with_abstract']} with an abstract, {stat['with_doi']} with a DOI, "
        f"{stat['uncategorized']} uncategorized")
    event("dataset_export", papers=len(recs), edges=bool(a.edges))


# ---- extract -------------------------------------------------------------
# The metadata library says which papers exist. These two say what is *in* them:
# the statements, the problems, the bounds. Both are stores, not deliverables;
# `run.py examples` exports them.
EXAMPLES, EXTRACTIONS = ROOT / "papers" / "examples.jsonl", ROOT / "papers" / "extractions.jsonl"
SAVE_EVERY_PAPERS = 5
RELSYM = {"contained-in": "⊆", "not-contained-in": "⊄", "strictly-contained-in": "⊊",
          "contains": "⊇", "separated-from": "≠", "equals": "="}


def _spread(pool, key, limit):
    """Round-robin by primary subarea: a batch drawn from one area measures one area."""
    buckets = defaultdict(list)
    for r in pool: buckets[key(r)].append(r)
    out, order = [], sorted(buckets)
    while len(out) < limit and any(buckets[k] for k in order):
        for k in order:
            if buckets[k]: out.append(buckets[k].pop(0))
            if len(out) >= limit: break
    return out


def _rank(r):
    """Screened-in first, then target venues, then citations — same order as screening."""
    return ({"included": 0, "candidate": 1}.get(r.get("status"), 2),
            {"target": 0, "other": 1, "unknown": 2}[tier(r)],
            -(r.get("cited_by_count") or 0), -(r.get("year") or 0), r.get("id", ""))


def select(st, a, done):
    pool = [r for r in st.recs.values() if r.get("arxiv_id")]
    if a.arxiv_id: return [r for r in pool if r["arxiv_id"] in set(a.arxiv_id)]
    if a.status: pool = [r for r in pool if r.get("status") == a.status]
    if a.category: pool = [r for r in pool if a.category in (r.get("categories") or categorize(r))]
    if not a.refresh: pool = [r for r in pool if r["id"] not in done]
    pool.sort(key=_rank)
    if a.no_spread: return pool[:a.limit]
    return _spread(pool, lambda r: ((r.get("categories") or categorize(r)) or ["uncategorized"])[0], a.limit)


def _example_row(r, it, d):
    return {"example_id": f"{r['arxiv_id']}#{it['ordinal']}", "paper_id": r["id"],
            "arxiv_id": r["arxiv_id"], "doi": r.get("doi", ""), "paper_title": r.get("title", ""),
            "year": r.get("year"), "venue_short": r.get("venue_short", ""), "venue_tier": tier(r),
            "categories": r.get("categories") or categorize(r),
            "source_sha256": d["source_sha256"], **it}


def extract_cmd(a):
    st = Store()
    exts = {r["paper_id"]: r for r in load_jsonl(EXTRACTIONS)}
    by_paper = defaultdict(list)
    for e in load_jsonl(EXAMPLES): by_paper[e["paper_id"]].append(e)
    todo = select(st, a, set(exts))
    log(f"{len(todo)} papers selected; {len(exts)} already extracted, {sum(len(v) for v in by_paper.values())} examples on file")
    seen, today = Counter(), time.strftime("%Y-%m-%d")

    def flush():
        save_jsonl(EXTRACTIONS, sorted(exts.values(), key=lambda r: r["paper_id"]))
        save_jsonl(EXAMPLES, [e for p in sorted(by_paper) for e in by_paper[p]])

    for i, r in enumerate(todo, 1):
        aid = r["arxiv_id"]
        if a.no_fetch and not FT.blob_path(aid).exists():
            seen["not-fetched"] += 1; continue
        try:
            d = FT.source_for(aid)
        except Exception as e:                      # one bad tarball must not end the run
            log(f"{aid}: {type(e).__name__}: {e}")
            event("extract_failed", arxiv_id=aid, error=f"{type(e).__name__}: {e}")
            d = {"status": "error", "src": "", "files": {}, "macros": {},
                 "blob_sha256": "", "source_sha256": ""}
        rec = {"paper_id": r["id"], "arxiv_id": aid, "title": r.get("title", ""),
               "year": r.get("year"), "status": d["status"], "blob_sha256": d["blob_sha256"],
               "source_sha256": d["source_sha256"], "source_chars": len(d["src"]),
               "extracted_at": today, "n_examples": 0,
               "categories": r.get("categories") or categorize(r)}
        if d["status"] == FT.OK:
            try:
                items = EX.extract(d["src"], d["files"], d["macros"])
                cls, prob, hyp = EX.paper_terms(d["src"], d["macros"])
            except Exception as e:
                log(f"{aid}: extract failed: {type(e).__name__}: {e}")
                event("extract_failed", arxiv_id=aid, error=f"{type(e).__name__}: {e}")
                rec["status"] = "extract-error"; exts[r["id"]] = rec; seen["extract-error"] += 1; continue
            rec.update(n_examples=len(items), n_files=len(d["files"]), n_macros=len(d["macros"]),
                       classes_used=cls, problems_used=prob, hypotheses_used=hyp)
            by_paper[r["id"]] = [_example_row(r, it, d) for it in items]
        else:
            by_paper.pop(r["id"], None)
        exts[r["id"]] = rec; seen[rec["status"]] += 1
        log(f"[{i}/{len(todo)}] {aid} {rec['status']}: {rec['n_examples']} examples "
            f"({rec['source_chars']} chars)")
        if i % SAVE_EVERY_PAPERS == 0: flush()
    flush()
    n = sum(len(v) for v in by_paper.values())
    log(f"extract: {dict(seen)}; {n} examples over {len(exts)} papers")
    event("extract", selected=len(todo), outcomes=dict(seen), examples=n)


# ---- examples export -----------------------------------------------------
EXCOLS = ["example_id", "paper_id", "arxiv_id", "doi", "paper_title", "year", "venue_short",
          "venue_tier", "categories", "kind", "env", "label", "ordinal", "title",
          "statement_text", "classes", "problems", "hypotheses", "measures", "named_objects",
          "relations", "bounds", "problem_spec", "char_start", "char_end",
          "source_sha256", "statement_tex"]
PTCOLS = ["paper_id", "arxiv_id", "title", "year", "venue_short", "categories", "status",
          "n_examples", "source_chars", "classes_used", "problems_used", "hypotheses_used"]


def relstr(rl):
    mod = f"{rl.get('modifier')}-" if rl.get("modifier") else ""
    return (f"{rl['lhs']}{rl.get('lhs_arg') or ''} {RELSYM.get(rl['relation'], rl['relation'])} "
            f"{mod}{rl['rhs']}{rl.get('rhs_arg') or ''}")


def _counts(pairs, top=None):
    c = Counter(pairs)
    return dict(c.most_common(top) if top else c.most_common())


def examples_cmd(a):
    rows = load_jsonl(EXAMPLES)
    exts = load_jsonl(EXTRACTIONS)
    if not rows: return log("no examples extracted yet — run `run.py extract` first")
    if a.kind: rows = [r for r in rows if r["kind"] in set(a.kind)]
    rows.sort(key=lambda r: (r["arxiv_id"], r["ordinal"]))
    DATA.mkdir(parents=True, exist_ok=True)

    def flat(r):
        out = dict(r)
        out["categories"] = SEP.join(r.get("categories") or [])
        for k in ("classes", "problems", "hypotheses", "measures", "named_objects", "bounds"):
            out[k] = SEP.join(r.get(k) or [])
        out["relations"] = SEP.join(relstr(x) for x in (r.get("relations") or []))
        out["problem_spec"] = int(bool(r.get("problem_spec")))
        return out

    with (DATA / "examples.csv").open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=EXCOLS, extrasaction="ignore", lineterminator="\n")
        w.writeheader(); [w.writerow(flat(r)) for r in rows]
    with (DATA / "examples.jsonl").open("w", encoding="utf-8") as fh:
        for r in rows: fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")

    with (DATA / "paper_terms.csv").open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=PTCOLS, extrasaction="ignore", lineterminator="\n")
        w.writeheader()
        for e in sorted(exts, key=lambda r: r.get("arxiv_id", "")):
            w.writerow({**{k: e.get(k, "") for k in PTCOLS},
                        "categories": SEP.join(e.get("categories") or []),
                        "classes_used": SEP.join(f"{k}:{v}" for k, v in (e.get("classes_used") or {}).items()),
                        "problems_used": SEP.join(f"{k}:{v}" for k, v in (e.get("problems_used") or {}).items()),
                        "hypotheses_used": SEP.join(f"{k}:{v}" for k, v in (e.get("hypotheses_used") or {}).items())})

    rel = [x for r in rows for x in (r.get("relations") or [])]
    ok = [e for e in exts if e.get("status") == "ok"]
    stat = {
        "examples": len(rows),
        "papers_with_examples": len({r["paper_id"] for r in rows}),
        "papers_attempted": len(exts),
        "by_fetch_status": _counts(e.get("status", "?") for e in exts),
        "papers_with_source_no_examples": sum(1 for e in ok if not e.get("n_examples")),
        "examples_per_paper_median": (sorted(e.get("n_examples", 0) for e in ok)[len(ok) // 2] if ok else 0),
        "by_kind": _counts(r["kind"] for r in rows),
        "by_category": _counts(c for r in rows for c in (r.get("categories") or [])),
        "by_year": dict(sorted(Counter(r.get("year") or 0 for r in rows).items())),
        "by_venue_tier": _counts(r.get("venue_tier", "unknown") for r in rows),
        "with_classes": sum(1 for r in rows if r.get("classes")),
        "with_problems": sum(1 for r in rows if r.get("problems")),
        "with_hypotheses": sum(1 for r in rows if r.get("hypotheses")),
        "with_bounds": sum(1 for r in rows if r.get("bounds")),
        "with_relations": sum(1 for r in rows if r.get("relations")),
        "problem_specs": sum(1 for r in rows if r.get("problem_spec")),
        "relations": len(rel),
        "distinct_classes": len({c for r in rows for c in (r.get("classes") or [])}),
        "top_classes": _counts((c for r in rows for c in (r.get("classes") or [])), 40),
        "top_problems": _counts((p for r in rows for p in (r.get("problems") or [])), 40),
        "top_hypotheses": _counts((h for r in rows for h in (r.get("hypotheses") or [])), 25),
        "top_named_objects": _counts((o for r in rows for o in (r.get("named_objects") or [])), 40),
        "top_measures": _counts((m for r in rows for m in (r.get("measures") or [])), 20),
        "with_measures": sum(1 for r in rows if r.get("measures")),
        "by_relation": _counts(x["relation"] for x in rel),
        "top_relation_pairs": _counts((f"{x['lhs']} {RELSYM.get(x['relation'], '?')} {x['rhs']}" for x in rel), 30),
    }
    (DATA / "examples_stats.json").write_text(json.dumps(stat, ensure_ascii=False, indent=2) + "\n",
                                              encoding="utf-8")
    log(f"examples.csv: {len(rows)} examples from {stat['papers_with_examples']} papers; "
        f"{stat['relations']} relations, {stat['problem_specs']} problem specs")
    event("examples_export", examples=len(rows), papers=stat["papers_with_examples"])


# ---- tasks ---------------------------------------------------------------
# A test item is a statement with one span blanked out. The answer is that span,
# verbatim, so `prompt.replace("[MASK]", answer)` must give the statement back —
# which `verify` checks. Nothing is generated that is not already in the paper.
#
# Deliberately absent: true/false items made by flipping a relation. Flipping
# `P ⊆ NP` to `P ⊄ NP` does not produce a falsehood, it produces an open
# problem, and labelling it "false" would be fabrication.
MASK = "[MASK]"
PER_PAPER = 4           # one paper must not become the benchmark
MIN_PROMPT = 60


def _mask_once(text, needle):
    """Blank the first occurrence of `needle`, tolerating whitespace drift."""
    if not needle.strip(): return None, None
    pat = re.compile(r"\s*".join(re.escape(t) for t in needle.split()))
    m = pat.search(text)
    if not m: return None, None
    return text[:m.start()] + MASK + text[m.end():], m.group(0)


def tasks_cmd(a):
    rows = load_jsonl(EXAMPLES)
    if not rows: return log("no examples on file — run `run.py extract` first")
    out, per = [], Counter()

    def add(kind, r, prompt, answer, **extra):
        if len(prompt) < MIN_PROMPT or prompt.count(MASK) != 1: return
        key = (r["paper_id"], kind)
        if per[key] >= PER_PAPER: return
        per[key] += 1
        out.append({"task_id": f"{r['example_id']}:{kind}:{per[key]}", "type": kind,
                    "example_id": r["example_id"], "paper_id": r["paper_id"],
                    "arxiv_id": r["arxiv_id"], "kind": r["kind"],
                    "categories": r.get("categories") or [], "prompt": prompt,
                    "answer": answer, "source_field": "statement_text", **extra})

    for r in sorted(rows, key=lambda r: (r["arxiv_id"], r["ordinal"])):
        text = r["statement_text"]
        for b in (r.get("bounds") or [])[:2]:
            p, hit = _mask_once(text, EX.detex(b, limit=200))
            if p: add("bound-cloze", r, p, hit, masked=b); break
        for rel in (r.get("relations") or [])[:2]:
            if not (rel.get("lhs_known") and rel.get("rhs_known")): continue
            p, hit = _mask_once(text, rel["rhs_classes"][0])
            if p: add("class-cloze", r, p, hit, relation=relstr(rel)); break
        # Which relation does the paper prove? Only the non-equality symbols:
        # "=" occurs in every other formula and would not identify the claim.
        syms = {RELSYM[x["relation"]] for x in (r.get("relations") or [])
                if x["relation"] != "equals"}
        if len(syms) == 1 and text.count(s := syms.pop()) == 1:
            p, hit = _mask_once(text, s)
            if p: add("relation-cloze", r, p, hit)
        if r.get("problem_spec"):
            for nm in (r.get("named_objects") or [])[:2]:
                p, hit = _mask_once(text, nm)
                if p: add("problem-name", r, p, hit); break
        if r["kind"] in ("theorem", "corollary", "lemma") and (r.get("categories")):
            add("subarea", r, text + f"\n\n{MASK}", SEP.join(r["categories"]))

    DATA.mkdir(parents=True, exist_ok=True)
    save_jsonl(DATA / "tasks.jsonl", out)
    with (DATA / "tasks.csv").open("w", encoding="utf-8", newline="") as fh:
        cols = ["task_id", "type", "example_id", "arxiv_id", "kind", "categories", "prompt", "answer"]
        w = csv.DictWriter(fh, fieldnames=cols, extrasaction="ignore", lineterminator="\n")
        w.writeheader()
        for t in out: w.writerow({**t, "categories": SEP.join(t["categories"])})
    log(f"tasks.jsonl: {len(out)} items — {dict(Counter(t['type'] for t in out))}")
    event("tasks_export", items=len(out), by_type=dict(Counter(t["type"] for t in out)))


def verify_tasks(examples_by_id):
    """A cloze item must reconstruct its statement exactly. No answer is invented."""
    probs, items = [], load_jsonl(DATA / "tasks.jsonl")
    for t in items:
        e = examples_by_id.get(t["example_id"])
        if e is None:
            probs.append(("ERROR", f"{t['task_id']}: no such example {t['example_id']}")); continue
        if t["type"] == "subarea":
            if t["answer"] != SEP.join(e.get("categories") or []):
                probs.append(("ERROR", f"{t['task_id']}: answer is not the paper's subareas"))
            continue
        if t["prompt"].replace(MASK, t["answer"]) != e["statement_text"]:
            probs.append(("ERROR", f"{t['task_id']}: prompt+answer does not rebuild the statement"))
    return probs, len(items)


def verify_examples():
    """Every statement must still be a byte-exact slice of the cached source.

    This is the same gate as the DOI check, one level down: a statement that
    cannot be located in the paper it claims to come from is a fabrication,
    whether a model wrote it or a parser did.
    """
    probs, exts = [], {r["paper_id"]: r for r in load_jsonl(EXTRACTIONS)}
    rows = load_jsonl(EXAMPLES)
    if not rows and not exts: return probs, 0
    by_paper = defaultdict(list)
    for e in rows: by_paper[e["paper_id"]].append(e)
    checked = 0
    for pid, items in sorted(by_paper.items()):
        rec = exts.get(pid)
        if rec is None:
            probs.append(("ERROR", f"{pid}: {len(items)} examples but no extraction record")); continue
        aid = rec["arxiv_id"]
        if not FT.blob_path(aid).exists():
            probs.append(("WARN", f"{aid}: source blob not cached; cannot re-check {len(items)} examples")); continue
        blob = FT.blob_path(aid).read_bytes()
        if FT.sha256(blob) != rec.get("blob_sha256"):
            probs.append(("ERROR", f"{aid}: cached blob changed since extraction")); continue
        src, _, _ = FT.normalized_source(blob)
        if FT.sha256(src) != rec.get("source_sha256"):
            probs.append(("ERROR", f"{aid}: normalized source does not reproduce")); continue
        for e in items:
            checked += 1
            got = src[e["char_start"]:e["char_end"]]
            if got != e["statement_tex"]:
                probs.append(("ERROR", f"{e['example_id']}: statement is not at the recorded offsets"))
            elif not e["statement_text"].strip():
                probs.append(("WARN", f"{e['example_id']}: empty rendered statement"))
            if e.get("kind") not in EX.KEEP:
                probs.append(("ERROR", f"{e['example_id']}: kind {e.get('kind')!r} is not an extractable kind"))
    orphan = sum(1 for p in by_paper if p not in exts)
    if orphan: probs.append(("WARN", f"{orphan} papers have examples but no extraction record"))
    tp, nt = verify_tasks({e["example_id"]: e for e in rows})
    if nt: print(f"re-checked {nt} test items against their statements")
    return probs + tp, checked


# ---- verify --------------------------------------------------------------
def verify(a):
    """The anti-fabrication gate. This field's canonical results have names, and
    a name is enough to reconstruct a citation that looks right and is wrong."""
    st = Store(); papers = st.by_status("included")
    probs, checked = (verify_examples() if (a.examples or a.all) else ([], 0))
    if checked: print(f"re-checked {checked} extracted statements against the cached sources")
    if not papers:
        if not probs and not checked: return print("nothing to verify: no included papers, no examples")
        papers = []
    for k, n in Counter(r.get("citekey", "") for r in papers).items():
        if not k: probs.append(("ERROR", f"{n} included paper(s) have no citekey"))
        elif n > 1: probs.append(("ERROR", f"citekey {k!r} used by {n} papers"))
    for r in papers:
        l = r.get("citekey") or r["id"]
        if not r.get("sources"): probs.append(("ERROR", f"{l}: no source — fetched, or invented?"))
        if not r.get("abstract"): probs.append(("ERROR", f"{l}: no abstract; screening was not grounded"))
        if not r.get("doi") and not r.get("arxiv_id"): probs.append(("WARN", f"{l}: no DOI/arXiv id to verify"))
        if not r.get("year"): probs.append(("WARN", f"{l}: no year"))
        if not r.get("reason"): probs.append(("WARN", f"{l}: included with no reason"))

    if not a.offline:
        pool = [r for r in papers if r.get("doi") or r.get("arxiv_id")]
        if not a.all and a.sample < len(pool): pool = random.sample(pool, a.sample)
        for r in pool:
            l = r.get("citekey") or r["id"]
            if r.get("doi"):
                try: m = (getj(f"{S.CR}/{r['doi']}").get("message") or {})
                except Exception as e: probs.append(("ERROR", f"{l}: DOI {r['doi']} did not resolve ({e})")); continue
                ts = m.get("title") or []
                if not ts: probs.append(("WARN", f"{l}: Crossref returned no title")); continue
                if (s := tsim(ts[0], r.get("title", ""))) < .8:
                    probs.append(("ERROR", f"{l}: DOI {r['doi']} resolves to {ts[0]!r}, "
                                           f"we stored {r.get('title')!r} (overlap {s:.2f})"))
                p = ((m.get("issued") or {}).get("date-parts") or [[None]])[0]
                if p and p[0] and r.get("year") and abs(int(p[0]) - int(r["year"])) > 1:
                    probs.append(("WARN", f"{l}: year {r['year']} but Crossref says {p[0]}"))
            else:
                try:
                    e = ET.fromstring(get(S.AX, {"id_list": r["arxiv_id"], "max_results": 1},
                                          headers={"Accept": "application/atom+xml"})).find("atom:entry", S.NS)
                except Exception as x: probs.append(("ERROR", f"{l}: arXiv lookup failed ({x})")); continue
                if e is None: probs.append(("ERROR", f"{l}: arXiv id {r['arxiv_id']} does not exist")); continue
                lt = e.findtext("atom:title", "", S.NS)
                if (s := tsim(lt, r.get("title", ""))) < .8:
                    probs.append(("ERROR", f"{l}: arXiv {r['arxiv_id']} is {lt.strip()!r}, "
                                           f"we stored {r.get('title')!r} (overlap {s:.2f})"))

    g = defaultdict(list)
    for lvl, m in probs: g[lvl].append(m)
    for lvl in ("ERROR", "WARN"):
        for m in g[lvl]: print(f"{lvl}: {m}")
    e, w = len(g["ERROR"]), len(g["WARN"])
    print(f"\nverified {len(papers)} included papers and {checked} statements: {e} errors, {w} warnings")
    event("verify", papers=len(papers), statements=checked, errors=e, warnings=w)
    sys.exit(1 if e else 0)


# ---- CLI -----------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    h = sub.add_parser("harvest"); h.set_defaults(f=harvest)
    h.add_argument("--query", action="append", default=[]); h.add_argument("--queries-file")
    h.add_argument("--max", type=int, default=100)
    h.add_argument("--from-year", type=int, default=0)  # the anchors predate arXiv
    h.add_argument("--categories", default=",".join(S.CATS)); h.add_argument("--no-topic-gate", action="store_true")

    e = sub.add_parser("enrich"); e.set_defaults(f=enrich)
    e.add_argument("--status"); e.add_argument("--skip-arxiv", action="store_true")
    e.add_argument("--skip-title-match", action="store_true")

    s = sub.add_parser("screen"); s.set_defaults(f=screen)
    s.add_argument("action", choices=["next", "apply", "stats"])
    s.add_argument("file", nargs="?"); s.add_argument("--limit", type=int, default=25)
    s.add_argument("--venue-tier", choices=["target", "other", "unknown"]); s.add_argument("--category")

    n = sub.add_parser("snowball"); n.set_defaults(f=snowball)
    n.add_argument("--seed-status", default="included")
    n.add_argument("--direction", choices=["backward", "forward", "both"], default="both")
    n.add_argument("--from-year", type=int, default=0); n.add_argument("--max-forward", type=int, default=50)
    n.add_argument("--no-topic-gate", action="store_true")

    d = sub.add_parser("dataset"); d.set_defaults(f=dataset)
    d.add_argument("--status"); d.add_argument("--edges", action="store_true")

    x = sub.add_parser("extract", help="fetch arXiv source and lift out statements")
    x.set_defaults(f=extract_cmd)
    x.add_argument("--limit", type=int, default=25); x.add_argument("--status")
    x.add_argument("--category"); x.add_argument("--arxiv-id", action="append", default=[])
    x.add_argument("--refresh", action="store_true", help="re-extract papers already done")
    x.add_argument("--no-spread", action="store_true", help="rank order instead of round-robin by subarea")
    x.add_argument("--no-fetch", action="store_true", help="only papers whose source is already cached")

    xe = sub.add_parser("examples", help="export the extracted statements"); xe.set_defaults(f=examples_cmd)
    xe.add_argument("--kind", action="append", default=[])

    tk = sub.add_parser("tasks", help="derive masked test items from the statements")
    tk.set_defaults(f=tasks_cmd)

    v = sub.add_parser("verify"); v.set_defaults(f=verify)
    v.add_argument("--all", action="store_true"); v.add_argument("--sample", type=int, default=25)
    v.add_argument("--offline", action="store_true")
    v.add_argument("--examples", action="store_true", help="re-check statements against cached sources")

    a = ap.parse_args()
    (stats if getattr(a, "action", None) == "stats" else a.f)(a)


if __name__ == "__main__":
    main()
