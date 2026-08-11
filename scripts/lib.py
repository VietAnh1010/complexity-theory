"""HTTP+cache, normalization, venue table, JSONL store. Subject-agnostic."""
from __future__ import annotations
import hashlib, json, os, re, sys, time, unicodedata
import urllib.error, urllib.parse, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CACHE, LIB = ROOT / ".cache", ROOT / "papers" / "library.jsonl"
LOGS, DATA = ROOT / "logs", ROOT / "dataset"
CONTACT = os.environ.get("SURVEY_CONTACT_EMAIL", "vietanh101003@gmail.com")
UA = f"complexity-theory-dataset/0.1 (mailto:{CONTACT})"
# arXiv 429s partway through a ~100-query pass at its documented 3s floor.
RATES = {"export.arxiv.org": float(os.environ.get("ARXIV_RATE_SECONDS", "3.0")),
         "api.crossref.org": .5, "api.opencitations.net": 1.}
_last: dict[str, float] = {}


def log(m): print(f"[{time.strftime('%H:%M:%S')}] {m}", file=sys.stderr, flush=True)


def event(kind, **f):
    LOGS.mkdir(parents=True, exist_ok=True)
    rec = {"ts": time.strftime("%Y-%m-%dT%H:%M:%S"), "kind": kind, **f}
    with (LOGS / "events.jsonl").open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(rec, ensure_ascii=False) + "\n")


class FetchError(RuntimeError): pass


def get(url, params=None, *, headers=None, retries=5, timeout=60):
    """GET with on-disk cache keyed by full URL. 4xx except 429 is permanent."""
    if params:
        url = f"{url}?{urllib.parse.urlencode(params, safe=':,>|<*')}"
    host = urllib.parse.urlparse(url).netloc or "x"
    cf = CACHE / host / f"{hashlib.sha256(url.encode()).hexdigest()[:24]}.json"
    if cf.exists():
        try: return json.loads(cf.read_text("utf-8"))["body"]
        except Exception: cf.unlink(missing_ok=True)
    h = {"User-Agent": UA, "Accept": "application/json", **(headers or {})}
    wait = 2.
    for i in range(1, retries + 1):
        gap = RATES.get(host, 1.); el = time.monotonic() - _last.get(host, 0)
        if el < gap: time.sleep(gap - el)
        _last[host] = time.monotonic()
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=h), timeout=timeout) as r:
                body = r.read().decode("utf-8", "replace")
            cf.parent.mkdir(parents=True, exist_ok=True)
            cf.write_text(json.dumps({"url": url, "fetched": time.time(), "body": body}), encoding="utf-8")
            return body
        except urllib.error.HTTPError as e:
            if e.code != 429 and e.code < 500:
                raise FetchError(f"HTTP {e.code} for {url}") from e
            wait = float(e.headers.get("Retry-After") or wait)
            log(f"HTTP {e.code} {host} {i}/{retries} in {wait:.0f}s"); time.sleep(wait)
        except (urllib.error.URLError, TimeoutError, OSError) as e:
            log(f"net {e} {i}/{retries} in {wait:.0f}s"); time.sleep(wait)
        wait = min(wait * 2, 120)
    event("fetch_failed", url=url)
    raise FetchError(f"gave up on {url}")


def getj(url, params=None, **kw): return json.loads(get(url, params, **kw))


def chunk(xs, n):
    for i in range(0, len(xs), n): yield xs[i:i + n]


def load_jsonl(path):
    if not Path(path).exists(): return []
    out = []
    for n, line in enumerate(Path(path).read_text("utf-8").splitlines(), 1):
        if not line.strip(): continue
        try: out.append(json.loads(line))
        except json.JSONDecodeError: log(f"bad line {n} in {path}")
    return out


def save_jsonl(path, rows):
    """Atomic, like Store.save: a crash mid-write must not truncate the file."""
    p = Path(path); p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(p.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as fh:
        for r in rows: fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    tmp.replace(p)


# ---- normalization -------------------------------------------------------
_WS, _NA, _TAG = re.compile(r"\s+"), re.compile(r"[^a-z0-9 ]+"), re.compile(r"<[^>]+>")


def clean(v): return _WS.sub(" ", unicodedata.normalize("NFKC", v)).strip() if v else ""


def strip_markup(m):
    """Crossref deposits <i>/<sub>/MathML inside *titles*; left in, dedup breaks."""
    if not m: return ""
    t = _TAG.sub(" ", m)
    for a, b in (("&amp;", "&"), ("&lt;", "<"), ("&gt;", ">"), ("&quot;", '"'), ("&apos;", "'")):
        t = t.replace(a, b)
    return clean(t)


def strip_jats(m): return re.sub(r"^\s*abstract[:\s]*", "", strip_markup(m), flags=re.I)


def ntitle(t): return _WS.sub(" ", _NA.sub(" ", clean(t).lower())).strip()


def tsim(a, b):
    """Token overlap on normalized titles; robust to subtitle/punctuation drift."""
    x, y = set(ntitle(a).split()), set(ntitle(b).split())
    return len(x & y) / max(len(x), len(y)) if x and y else 0.


def ndoi(d):
    if not d: return ""
    d = re.sub(r"^(https?://)?(dx\.)?doi\.org/", "", clean(d).lower())
    return d.removeprefix("doi:").strip()


def narxiv(v):
    if not v: return ""
    m = re.search(r"(\d{4}\.\d{4,5})(v\d+)?", v) or re.search(r"([a-z-]+(\.[A-Z]{2})?/\d{7})(v\d+)?", v)
    return m.group(1) if m else ""


def aliases(r):
    out = []
    if r.get("doi"): out.append(f"doi:{r['doi']}")
    if r.get("arxiv_id"): out.append(f"arxiv:{r['arxiv_id']}")
    if (t := ntitle(r.get("title"))): out.append(f"title:{t}")
    return out


def rid(r):
    for a in aliases(r):
        if not a.startswith("title:"): return a
    t = ntitle(r.get("title"))
    if not t: raise ValueError("no identifier and no title")
    return "title:" + hashlib.sha1(t.encode()).hexdigest()[:12]


# ---- venues --------------------------------------------------------------
# Order matters. ECCC precedes CC (both contain "computational complexity",
# and ECCC is a preprint server, not the journal). LMCS before LICS.
VENUES = {
    "STOC": r"\bstoc\b|symposium on (the )?theory of computing|theory of computing conference",
    "FOCS": r"\bfocs\b|foundations of computer science",
    "CCC": r"\bccc\b|(conference on )?computational complexity conference|conference on computational complexity",
    "SODA": r"\bsoda\b|symposium on discrete algorithms",
    "ITCS": r"\bitcs\b|innovations in theoretical computer science",
    "ICALP": r"\bicalp\b|automata, languages,? and programming",
    "APPROX": r"\bapprox\b|approximation algorithms for combinatorial",
    "RANDOM": r"\brandom\b.{0,40}\b(workshop|international)|randomization and computation",
    "ESA": r"\besa\b|european symposium on algorithms",
    "MFCS": r"\bmfcs\b|mathematical foundations of computer science",
    "STACS": r"\bstacs\b|theoretical aspects of computer science",
    "IPEC": r"\bipec\b|parameterized and exact computation",
    "LMCS": r"logical methods in computer science|\blmcs\b",
    "LICS": r"\blics\b|logic in computer science",
    "CSL": r"\bcsl\b|computer science logic",
    "QIP": r"\bqip\b|quantum information processing",
    "TQC": r"\btqc\b|theory of quantum computation",
    "ITC": r"\bitc\b|information[- ]theoretic cryptography",
    "CSR": r"\bcsr\b|computer science.{0,5}theory and applications|international computer science symposium in russia",
    "CRYPTO": r"\bcrypto\b(?!graph)|advances in cryptology.*crypto",
    "EUROCRYPT": r"\beurocrypt\b",
    "TCC": r"\btcc\b|theory of cryptography conference",
    "QIC": r"quantum information (and|&) computation",
    "ACM-TQC": r"transactions on quantum computing",
    "Quantum": r"^quantum[ ,]\s*\d",
    "JML": r"journal of mathematical logic",
    "JACM": r"journal of the acm|\bjacm\b",
    "SICOMP": r"siam journal on computing|\bsicomp\b",
    "ToC": r"\btheory of computing\b(?!.*conference)",
    "TheoretiCS": r"\btheoretics\b",
    "ECCC": r"electronic colloquium on computational complexity|\beccc\b",
    "CC": r"^computational complexity\b|\bjournal of computational complexity\b",
    "TOCT": r"transactions on computation theory|\btoct\b",
    "JCSS": r"journal of computer and system sciences|\bjcss\b",
    "IandC": r"information and (computation|control)",
    "TCS": r"\btheoretical computer science\b",
    "Combinatorica": r"\bcombinatorica\b",
    "arXiv": r"\barxiv\b|corr",
}
TARGET = {"STOC", "FOCS", "CCC", "SODA", "ITCS", "ICALP", "JACM", "SICOMP", "ToC", "CC"}
# A preprint server is not the committee; enrichment must read these as empty.
PLACEHOLDER = {"arxiv", "corr", "arxiv preprint", "preprint", "eccc",
               "electronic colloquium on computational complexity"}
_V = [(n, re.compile(p, re.I)) for n, p in VENUES.items()]


def venue(v):
    t = clean(v).lower()
    return next((n for n, p in _V if p.search(t)), "") if t else ""


def real_venue(r):
    v = clean(r.get("venue")).lower()
    return bool(v) and v not in PLACEHOLDER


def tier(r):
    c = r.get("venue_short") or venue(r.get("venue"))
    return "target" if c in TARGET else ("other" if c else "unknown")


# ---- store ---------------------------------------------------------------
CURATED = {"status", "reason", "tags", "categories", "citekey", "note_path", "screened_at", "priority"}
STATUSES = {"candidate", "included", "excluded", "unavailable"}
MERGE = ("sources", "discovered_via", "arxiv_categories")


class Store:
    """JSONL, not SQLite: greppable, diffable, recoverable after a mid-write crash."""

    def __init__(self, path=LIB):
        self.path, self.recs, self._ax = path, {}, {}
        if path.exists():
            for n, line in enumerate(path.read_text("utf-8").splitlines(), 1):
                if not line.strip(): continue
                try: r = json.loads(line)
                except json.JSONDecodeError: log(f"bad library line {n}"); continue
                self.recs[r["id"]] = r; self.index(r)

    def index(self, r):
        for a in aliases(r): self._ax.setdefault(a, r["id"])

    def find(self, r):
        return next((self._ax[a] for a in aliases(r) if a in self._ax), None)

    def upsert(self, r):
        """Fill gaps and union lists; never overwrite curated fields or non-empty scalars."""
        r = {k: v for k, v in r.items() if v not in (None, "", [], {})}
        now, eid = time.strftime("%Y-%m-%d"), self.find(r)
        if eid is None:
            r["id"] = rid(r); r.setdefault("status", "candidate")
            r.setdefault("first_seen", now); r["last_updated"] = now
            self.recs[r["id"]] = r; self.index(r)
            return r["id"], True
        cur = self.recs[eid]
        for k, v in r.items():
            if k in CURATED or k == "id": continue
            if k in MERGE: cur[k] = list(dict.fromkeys(cur.get(k, []) + list(v)))
            elif k == "venue" and not real_venue(cur):
                cur["venue"], cur["venue_short"] = v, venue(v)
            elif not cur.get(k): cur[k] = v
        cur["last_updated"] = now; self.index(cur)
        return eid, False

    def save(self):
        """Atomic: a crash mid-save must not truncate the library."""
        self.path.parent.mkdir(parents=True, exist_ok=True)
        tmp = self.path.with_suffix(".jsonl.tmp")
        rows = sorted(self.recs.values(), key=lambda r: (-(r.get("year") or 0), r.get("title", "")))
        with tmp.open("w", encoding="utf-8") as fh:
            for r in rows: fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
        tmp.replace(self.path)

    def by_status(self, s): return [r for r in self.recs.values() if r.get("status") == s]

    def counts(self):
        from collections import Counter
        return dict(Counter(r.get("status", "candidate") for r in self.recs.values()))


_STOP = {"a", "an", "the", "of", "for", "and", "on", "in", "to", "with", "via",
         "using", "towards", "toward", "by", "at", "from", "is", "are"}


def citekeys(store):
    """author+year+first content word, disambiguated a/b/c. Existing keys kept."""
    taken = {r["citekey"] for r in store.recs.values() if r.get("citekey")}
    for r in sorted(store.recs.values(), key=lambda r: r.get("first_seen", "")):
        if r.get("citekey"): continue
        au = r.get("authors") or []
        sur = (_NA.sub("", clean(au[0]).split()[-1].lower()) or "anon") if au and clean(au[0]).split() else "anon"
        word = next((w for w in ntitle(r.get("title")).split() if w not in _STOP and len(w) > 2), "paper")
        base = k = f"{sur}{r.get('year') or 'nd'}{word}"
        i = ord("a")
        while k in taken: k = f"{base}{chr(i)}"; i += 1
        taken.add(k); r["citekey"] = k
