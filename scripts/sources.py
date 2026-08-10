"""arXiv, Crossref, OpenCitations. All free, keyless, unmetered — keep it that way."""
from __future__ import annotations
import re, xml.etree.ElementTree as ET
from lib import (CONTACT, chunk, clean, get, getj, log, narxiv, ndoi,
                 strip_jats, strip_markup, tsim, venue)

AX = "http://export.arxiv.org/api/query"
NS = {"atom": "http://www.w3.org/2005/Atom", "arxiv": "http://arxiv.org/schemas/atom"}
CR = "https://api.crossref.org/works"
OC = "https://api.opencitations.net/index/v2/citations"
# cs.CC is the spine; the rest are where complexity cross-lists.
CATS = ["cs.CC", "cs.DS", "cs.DM", "cs.LO", "cs.CR", "cs.GT", "math.CO", "math.LO", "quant-ph"]
THRESH = .8  # title-match floor; a wrong match assigns a real paper the wrong DOI


# ---- arXiv ---------------------------------------------------------------
def _t(e, p):
    n = e.find(p, NS)
    return clean(n.text) if n is not None and n.text else ""


def ax_parse(e, via):
    if not (title := _t(e, "atom:title")): return None
    pub, jref = _t(e, "atom:published"), _t(e, "arxiv:journal_ref")
    v = jref or "arXiv"
    r = {"title": title,
         "authors": [clean(a.findtext("atom:name", "", NS)) for a in e.findall("atom:author", NS)],
         "year": int(pub[:4]) if pub[:4].isdigit() else None, "venue": v, "venue_short": venue(v),
         "arxiv_id": narxiv(_t(e, "atom:id")), "doi": ndoi(_t(e, "arxiv:doi")),
         "abstract": _t(e, "atom:summary"), "url": _t(e, "atom:id"),
         "pdf_url": next((l.get("href", "") for l in e.findall("atom:link", NS) if l.get("title") == "pdf"), ""),
         "arxiv_categories": [c.get("term", "") for c in e.findall("atom:category", NS)],
         "sources": ["arxiv"], "discovered_via": [via]}
    return {k: v for k, v in r.items() if v not in (None, "", [])}


def ax_search(q, cats, n):
    """Query files are plain phrases joined by AND; arXiv needs a field prefix."""
    if not re.search(r"\b(all|ti|abs|au|cat|co|jr|rn|id):", q):
        q = " AND ".join(f'all:"{p.strip()}"' for p in q.split(" AND ") if p.strip())
    sq = f"({q}) AND ({' OR '.join('cat:' + c for c in cats)})" if cats else q
    out, start = [], 0
    while len(out) < n:
        size = min(100, n - len(out))
        body = get(AX, {"search_query": sq, "start": start, "max_results": size,
                        "sortBy": "relevance", "sortOrder": "descending"},
                   headers={"Accept": "application/atom+xml"})
        page = ET.fromstring(body).findall("atom:entry", NS)
        out += page
        if len(page) < size: break
        start += size
    return out[:n]


def ax_by_ids(ids, via):
    out = []
    for b in chunk(list(dict.fromkeys(i for i in ids if i)), 100):
        try:
            es = ET.fromstring(get(AX, {"id_list": ",".join(b), "max_results": len(b)},
                                   headers={"Accept": "application/atom+xml"})).findall("atom:entry", NS)
        except Exception as e:
            log(f"arxiv id lookup failed for {len(b)}: {e}"); continue
        out += [r for r in (ax_parse(x, via) for x in es) if r]
    return out


def ax_by_title(title):
    """Recovers abstracts Crossref left blank. High threshold on purpose."""
    def cl(t): return re.sub(r"\s+", " ", re.sub(r"[^\w\s]", " ", t)).strip()
    probes = [cl(title)]
    head = cl(title.split(":")[0])
    if head != probes[0] and len(head.split()) >= 3: probes.append(head)
    best, score = None, 0.
    for p in (x for x in probes if len(x.split()) >= 3):
        try:
            es = ET.fromstring(get(AX, {"search_query": f'ti:"{p}"', "max_results": 5},
                                   headers={"Accept": "application/atom+xml"})).findall("atom:entry", NS)
        except Exception as e:
            log(f"arxiv title lookup failed {p[:40]!r}: {e}"); continue
        for r in (x for x in (ax_parse(e, "arxiv:title-match") for e in es) if x):
            if (s := tsim(r["title"], title)) > score: best, score = r, s
        if score >= THRESH: break
    return best if score >= THRESH else None


# ---- Crossref ------------------------------------------------------------
SELECT = "DOI,title,author,issued,container-title,event,abstract,URL,type,is-referenced-by-count,link"
BATCH = 40
SERIES = {"lecture notes in computer science", "lecture notes in artificial intelligence",
          "lecture notes in business information processing",
          "communications in computer and information science",
          "ifip advances in information and communication technology"}


def _cr_venue(it):
    """Whichever of event/container names a venue we know wins.

    Old ACM proceedings deposit an event.name identifying nothing — Natural
    Proofs carries "the twenty-sixth annual ACM symposium" while its container
    spells out STOC '94. Those old records are exactly what snowballing reaches.
    """
    ev = clean((it.get("event") or {}).get("name"))
    cs = [c for c in (clean(t) for t in it.get("container-title") or []) if c]
    if ev and venue(ev): return ev
    if (m := next((c for c in cs if venue(c)), None)): return m
    if ev: return ev
    if not cs: return ""
    spec = [c for c in cs if c.lower() not in SERIES]
    return spec[-1] if spec else cs[0]


def cr_parse(it, via):
    ts = it.get("title") or []
    if not (title := strip_markup(ts[0] if ts else "")): return None
    yr = next((p[0] for f in ("published", "issued", "published-print", "published-online")
               for p in [((it.get(f) or {}).get("date-parts") or [[None]])[0]] if p and p[0]), None)
    au = []
    for p in it.get("author") or []:
        if (n := clean(f"{p.get('given','')} {p.get('family','')}") or clean(p.get("name"))): au.append(n)
    v = _cr_venue(it)
    r = {"title": title, "authors": au, "year": int(yr) if yr else None, "venue": v,
         "venue_short": venue(v), "doi": ndoi(it.get("DOI")), "abstract": strip_jats(it.get("abstract")),
         "cited_by_count": it.get("is-referenced-by-count") or 0, "url": it.get("URL") or "",
         "pdf_url": next((l.get("URL", "") for l in it.get("link") or []
                          if l.get("content-type") == "application/pdf"), ""),
         "work_type": it.get("type") or "", "sources": ["crossref"], "discovered_via": [via]}
    return {k: v for k, v in r.items() if v not in (None, "", [], 0) or k in ("year", "cited_by_count")}


def cr_by_dois(dois, via):
    out = []
    for b in chunk(list(dict.fromkeys(dois)), BATCH):
        try:
            p = getj(CR, {"filter": ",".join(f"doi:{d}" for d in b), "select": SELECT,
                          "rows": len(b), "mailto": CONTACT})
        except Exception as e:
            log(f"crossref batch of {len(b)} failed: {e}"); continue
        out += [r for r in (cr_parse(i, via) for i in (p.get("message") or {}).get("items") or []) if r]
    return out


def cr_by_title(title, via):
    """Recovers the published DOI/venue for arXiv-only records. Low yield is the data."""
    if len(title.split()) < 3: return None
    try:
        p = getj(CR, {"query.title": title, "rows": 3, "select": SELECT, "mailto": CONTACT})
    except Exception as e:
        log(f"crossref title lookup failed {title[:40]!r}: {e}"); return None
    best, score = None, 0.
    for r in (x for x in (cr_parse(i, via) for i in (p.get("message") or {}).get("items") or []) if x):
        if (s := tsim(r["title"], title)) > score: best, score = r, s
    return best if score >= THRESH else None


def cr_refs(doi):
    """Cited DOIs, plus how many references were deposited without one."""
    refs = ((getj(f"{CR}/{doi}", {"mailto": CONTACT}).get("message") or {}).get("reference")) or []
    got = [ndoi(r["DOI"]) for r in refs if r.get("DOI")]
    return list(dict.fromkeys(got)), len(refs) - len(got)


# ---- OpenCitations -------------------------------------------------------
_D, _A = re.compile(r"doi:(\S+)"), re.compile(r"arxiv:(\S+)")


def oc_citing(doi):
    """Open citation data only: a thin result is thin data, not an uncited paper."""
    out = []
    for e in getj(f"{OC}/doi:{doi}") or []:
        c = e.get("citing") or ""
        d, a = _D.search(c), _A.search(c)
        if not d and not a: continue  # OMID only; nothing resolvable
        cr = e.get("creation") or ""
        out.append({"doi": ndoi(d.group(1)) if d else "", "arxiv_id": narxiv(a.group(1)) if a else "",
                    "year": int(cr[:4]) if cr[:4].isdigit() else None})
    return out
