"""One CLI for the pipeline. Every subcommand is idempotent and resumable.

    run.py harvest  --queries-file config/queries.txt --max 100
    run.py enrich
    run.py screen next --limit 25 | run.py screen apply decisions.json | run.py screen stats
    run.py snowball --seed-status included
    run.py dataset --edges
    run.py verify --all
"""
from __future__ import annotations
import argparse, csv, json, random, sys, time
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict

import sources as S
from lib import (DATA, STATUSES, Store, authors_agree, citekeys, event, get, getj,
                 log, ndoi, real_venue, strip_markup, tier, title_match, tsim, venue)
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
            p = S.cr_by_title(r["title"], "enrich:crossref-title", r.get("authors"))
            if not p or not p.get("doi") or st.find({"doi": p["doi"]}): continue
            event("title_matched", id=r["id"], doi=p["doi"], stored=r["title"], resolves_to=p["title"])
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

    # A title match that passed the old floor could assign a real paper another
    # paper's DOI ("Complexity of X" vs "Parameterised Complexity of X"). Re-check
    # every record that carries both a DOI and an arXiv id - the title-matched
    # population - and drop the DOI when the live title says it is a different paper.
    cleared = 0
    if not a.skip_doi_recheck:
        cand = [r for r in st.recs.values() if r.get("doi") and r.get("arxiv_id") and r.get("title")]
        log(f"crossref: re-checking {len(cand)} DOIs that came from a title match")
        for r in cand:
            try: m = (S.getj(f"{S.CR}/{r['doi']}", {"mailto": S.CONTACT}).get("message") or {})
            except Exception: continue          # unregistered or unreachable: verify reports it
            ts = [t for t in (m.get("title") or []) if t and t.strip()]
            # Crossref sometimes deposits no title at all; that is missing data,
            # not evidence of a wrong DOI.
            if not ts: continue
            cr = {"authors": [f"{a.get('given','')} {a.get('family','')}".strip()
                              for a in (m.get("author") or [])]}
            if title_match(strip_markup(ts[0]), r["title"]) and authors_agree(cr, r): continue
            log(f"  !! {r.get('citekey') or r['id']}: {r['doi']} is {ts[0]!r}; clearing")
            event("doi_cleared", id=r["id"], doi=r["doi"], resolves_to=ts[0], stored=r["title"])
            # Drop the alias too: left in place, the next paper carrying this DOI
            # would merge into this record.
            st._ax.pop(f"doi:{r['doi']}", None)
            r["doi"] = ""
            if not r.get("venue", "").lower().startswith("arxiv"):
                r["venue"], r["venue_short"] = "arXiv", "arXiv"
            cleared += 1

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
        f"{revised} venues revised, {retitled} titles cleaned, {cleared} wrong DOIs cleared")
    log(f"{na} still unscreenable (no abstract); {nd} cannot be snowballed from (no DOI)")
    event("enrich", crossref=filled, published=matched, arxiv=recovered, no_abstract=na,
          no_doi=nd, dois_cleared=cleared)


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
        "arxiv_categories", "status", "reason", "priority", "tags", "sources", "discovered_via",
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
                "tags": SEP.join(r.get("tags") or []),
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


# ---- verify --------------------------------------------------------------
def verify(a):
    """The anti-fabrication gate. This field's canonical results have names, and
    a name is enough to reconstruct a citation that looks right and is wrong."""
    st = Store(); papers = st.by_status("included")
    if not papers: return print("nothing to verify: no included papers")
    probs = []
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
            unresolved = ""
            if r.get("doi"):
                try: m = (getj(f"{S.CR}/{r['doi']}").get("message") or {})
                except Exception as e:
                    # A DOI registered ahead of publication 404s at Crossref. That is
                    # not a fabricated citation if an arXiv id verifies the title, so
                    # fall through to that check and warn. With no arXiv id to fall
                    # back on, nothing grounds the record and it stays an error.
                    if not r.get("arxiv_id"):
                        probs.append(("ERROR", f"{l}: DOI {r['doi']} did not resolve ({e})")); continue
                    unresolved = f"{l}: DOI {r['doi']} does not resolve; verified against arXiv instead"
                    m = {}
                ts = m.get("title") or []
                if not ts and not unresolved:
                    probs.append(("WARN", f"{l}: Crossref returned no title")); continue
                if ts and not title_match(ts[0], r.get("title", "")):
                    s = tsim(ts[0], r.get("title", ""))
                    probs.append(("ERROR", f"{l}: DOI {r['doi']} resolves to {ts[0]!r}, "
                                           f"we stored {r.get('title')!r} (overlap {s:.2f})"))
                p = ((m.get("issued") or {}).get("date-parts") or [[None]])[0]
                if p and p[0] and r.get("year") and abs(int(p[0]) - int(r["year"])) > 1:
                    probs.append(("WARN", f"{l}: year {r['year']} but Crossref says {p[0]}"))
            if unresolved or not r.get("doi"):
                if unresolved: probs.append(("WARN", unresolved))
                try:
                    e = ET.fromstring(get(S.AX, {"id_list": r["arxiv_id"], "max_results": 1},
                                          headers={"Accept": "application/atom+xml"})).find("atom:entry", S.NS)
                except Exception as x: probs.append(("ERROR", f"{l}: arXiv lookup failed ({x})")); continue
                if e is None: probs.append(("ERROR", f"{l}: arXiv id {r['arxiv_id']} does not exist")); continue
                lt = e.findtext("atom:title", "", S.NS)
                if not title_match(lt, r.get("title", "")):
                    s = tsim(lt, r.get("title", ""))
                    probs.append(("ERROR", f"{l}: arXiv {r['arxiv_id']} is {lt.strip()!r}, "
                                           f"we stored {r.get('title')!r} (overlap {s:.2f})"))

    g = defaultdict(list)
    for lvl, m in probs: g[lvl].append(m)
    for lvl in ("ERROR", "WARN"):
        for m in g[lvl]: print(f"{lvl}: {m}")
    e, w = len(g["ERROR"]), len(g["WARN"])
    print(f"\nverified {len(papers)} included papers: {e} errors, {w} warnings")
    event("verify", papers=len(papers), errors=e, warnings=w)
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
    e.add_argument("--skip-doi-recheck", action="store_true")

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

    v = sub.add_parser("verify"); v.set_defaults(f=verify)
    v.add_argument("--all", action="store_true"); v.add_argument("--sample", type=int, default=25)
    v.add_argument("--offline", action="store_true")

    a = ap.parse_args()
    (stats if getattr(a, "action", None) == "stats" else a.f)(a)


if __name__ == "__main__":
    main()
