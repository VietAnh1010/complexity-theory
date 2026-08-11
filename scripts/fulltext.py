"""arXiv e-print source: fetch, unpack, flatten, expand macros, de-TeX.

The abstract is not enough. What the authors actually *use* — the problems they
define, the classes they separate, the bounds they prove — lives in theorem and
definition environments in the LaTeX source, and arXiv serves that source.

Everything here is deterministic given the cached tarball, so `verify` can
re-derive the normalized source and check every extracted statement byte for
byte. Nothing is fetched twice: the blob is cached under `.cache/eprint/`.
"""
from __future__ import annotations
import gzip, hashlib, io, os, re, tarfile, time
import urllib.error, urllib.request
from pathlib import Path

from lib import CACHE, UA, event, log

EPRINT = "https://export.arxiv.org/e-print/"  # the host arXiv designates for automation
# arXiv asks for a wide gap on bulk source download; this is not the API floor.
RATE = float(os.environ.get("ARXIV_EPRINT_SECONDS", "8.0"))
MAXB = 40 << 20  # a 40MB source is figures, not theorems
_last = 0.0

TEXT_EXT = {".tex", ".sty", ".cls", ".tikz", ".inc", ".txt", ".ltx"}
# Fetch outcomes. Only "ok" carries source; the rest are data, not failures.
OK, PDF_ONLY, NO_TEX, TOO_BIG, GONE, ERROR = "ok", "pdf-only", "no-tex", "too-big", "gone", "error"


def blob_path(aid): return CACHE / "eprint" / (re.sub(r"[^\w.-]", "_", aid) + ".bin")


def meta_path(aid): return blob_path(aid).with_suffix(".status")


def fetch_eprint(aid, *, timeout=120, retries=4):
    """Cached GET of the e-print blob. Returns (status, bytes|None).

    A permanent 4xx is cached as a status file: arXiv has no source for some
    old submissions, and re-asking every run wastes the rate budget.
    """
    global _last
    bp, mp = blob_path(aid), meta_path(aid)
    if bp.exists(): return OK, bp.read_bytes()
    if mp.exists(): return mp.read_text("utf-8").strip(), None
    bp.parent.mkdir(parents=True, exist_ok=True)
    wait = 5.0
    for i in range(1, retries + 1):
        if (el := time.monotonic() - _last) < RATE: time.sleep(RATE - el)
        _last = time.monotonic()
        try:
            req = urllib.request.Request(EPRINT + aid, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                data = r.read(MAXB + 1)
            if len(data) > MAXB:
                mp.write_text(TOO_BIG, encoding="utf-8"); return TOO_BIG, None
            bp.write_bytes(data)
            return OK, data
        except urllib.error.HTTPError as e:
            if e.code in (403, 404, 410):
                mp.write_text(GONE, encoding="utf-8")
                event("eprint_gone", arxiv_id=aid, code=e.code); return GONE, None
            if e.code != 429 and e.code < 500:
                mp.write_text(ERROR, encoding="utf-8")
                event("eprint_error", arxiv_id=aid, code=e.code); return ERROR, None
            wait = float(e.headers.get("Retry-After") or wait)
            log(f"eprint HTTP {e.code} {aid} {i}/{retries} in {wait:.0f}s"); time.sleep(wait)
        except (urllib.error.URLError, TimeoutError, OSError) as e:
            log(f"eprint net {aid} {e} {i}/{retries} in {wait:.0f}s"); time.sleep(wait)
        wait = min(wait * 2, 120)
    event("eprint_failed", arxiv_id=aid)
    return ERROR, None


# ---- unpack --------------------------------------------------------------
def _decode(b):
    for enc in ("utf-8", "latin-1"):
        try: return b.decode(enc)
        except UnicodeDecodeError: continue
    return b.decode("utf-8", "replace")


def unpack(blob):
    """Blob -> {name: text} for the text-ish members. Handles tar.gz, bare gz, plain."""
    if blob[:4] == b"%PDF": return {}
    files = {}
    try:
        with tarfile.open(fileobj=io.BytesIO(blob), mode="r:*") as tf:
            for m in tf.getmembers():
                if not m.isfile() or m.size > (8 << 20): continue
                if Path(m.name).suffix.lower() not in TEXT_EXT: continue
                fh = tf.extractfile(m)
                if fh is not None: files[m.name] = _decode(fh.read())
        return files
    except tarfile.TarError:
        pass
    try:
        raw = gzip.decompress(blob)
    except (OSError, EOFError):
        raw = blob
    if raw[:4] == b"%PDF": return {}
    text = _decode(raw)
    return {"main.tex": text} if "\\" in text[:4000] else {}


# ---- LaTeX plumbing ------------------------------------------------------
_COMMENT = re.compile(r"(?<!\\)((?:\\\\)*)%.*")


def strip_comments(text):
    """Drop `%` comments, keeping `\\%`. Line structure is preserved."""
    return "\n".join(_COMMENT.sub(r"\1", ln) for ln in text.replace("\r\n", "\n").split("\n"))


def group_at(text, i):
    """Read a balanced {...} starting at text[i]=='{'. Returns (body, end_index)."""
    if i >= len(text) or text[i] != "{": return None, i
    depth, j = 0, i
    while j < len(text):
        c = text[j]
        if c == "\\": j += 2; continue
        if c == "{": depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0: return text[i + 1:j], j + 1
        j += 1
    return None, i


def opt_at(text, i):
    """Read a [...] optional argument starting at text[i]=='['."""
    if i >= len(text) or text[i] != "[": return None, i
    depth, j = 0, i
    while j < len(text):
        c = text[j]
        if c == "\\": j += 2; continue
        if c == "[": depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0: return text[i + 1:j], j + 1
        j += 1
    return None, i


def _resolve(files, name):
    """\\input{x} names a file that may or may not carry its extension."""
    cands = [name, name + ".tex", name + ".TEX"]
    low = {k.lower(): k for k in files}
    for c in cands:
        c = c.strip().lstrip("./")
        for k in (c, low.get(c.lower())):
            if k and k in files: return k
        for k in files:  # tarballs carry a leading directory component
            if k.endswith("/" + c) or k.lower().endswith("/" + c.lower()): return k
    return None


_INPUT = re.compile(r"\\(input|include|subfile)\s*(\{|\s)")


def flatten(files, name, seen=None, depth=0):
    """Splice \\input/\\include children in place. Cycles and depth are capped."""
    seen = seen if seen is not None else set()
    if name in seen or depth > 8 or name not in files: return ""
    seen.add(name)
    text, out, i = strip_comments(files[name]), [], 0
    while (m := _INPUT.search(text, i)):
        out.append(text[i:m.start()])
        if m.group(2) == "{":
            arg, end = group_at(text, m.end() - 1)
        else:  # \input plainname
            m2 = re.compile(r"\s*([\w./-]+)").match(text, m.end() - 1)
            arg, end = (m2.group(1), m2.end()) if m2 else (None, m.end())
        child = _resolve(files, arg) if arg else None
        if child: out.append(flatten(files, child, seen, depth + 1))
        i = end
    out.append(text[i:])
    return "".join(out)


def main_tex(files):
    """The file with \\begin{document}; ties broken by \\documentclass then size."""
    cands = [n for n, t in files.items()
             if n.lower().endswith((".tex", ".ltx")) and "\\begin{document}" in t]
    if not cands:
        cands = [n for n in files if n.lower().endswith((".tex", ".ltx"))]
    if not cands: return None
    return max(cands, key=lambda n: ("\\documentclass" in files[n], len(files[n])))


# ---- macros --------------------------------------------------------------
_NEWCMD = re.compile(r"\\(newcommand|renewcommand|providecommand|DeclareRobustCommand)\s*\*?\s*"
                     r"(?:\{\s*\\([A-Za-z@]+)\s*\}|\\([A-Za-z@]+))")
_DEF = re.compile(r"\\(?:def|gdef|edef)\s*\\([A-Za-z@]+)\s*(?=\{)")
_MATHOP = re.compile(r"\\DeclareMathOperator\s*\*?\s*\{\s*\\([A-Za-z@]+)\s*\}")


def collect_macros(files):
    """Author macro table. `\\cc{S_2E}` is unreadable and unmatchable until expanded."""
    macros = {}
    for name, raw in files.items():
        text = strip_comments(raw)
        for m in _NEWCMD.finditer(text):
            nm, j = m.group(2) or m.group(3), m.end()
            nargs, dflt = 0, None
            o, j2 = opt_at(text, j) if j < len(text) and text[j] == "[" else (None, j)
            if o is not None and o.strip().isdigit(): nargs, j = int(o.strip()), j2
            if j < len(text) and text[j] == "[":
                dflt, j = opt_at(text, j)
            body, end = group_at(text, j) if j < len(text) and text[j] == "{" else (None, j)
            if body is None: continue
            macros.setdefault(nm, (nargs, dflt, body))
        for m in _MATHOP.finditer(text):
            body, end = group_at(text, m.end())
            if body is not None: macros.setdefault(m.group(1), (0, None, r"\mathrm{" + body + "}"))
        for m in _DEF.finditer(text):
            body, end = group_at(text, m.end())
            if body is not None: macros.setdefault(m.group(1), (0, None, body))
    return macros


_CALL = re.compile(r"\\([A-Za-z@]+)")


def expand(text, macros, *, rounds=6, limit=200_000):
    """Expand author macros to a fixpoint (capped). Unknown control words are left alone."""
    for _ in range(rounds):
        out, i, hit = [], 0, False
        while (m := _CALL.search(text, i)):
            nm = m.group(1)
            spec = macros.get(nm)
            if spec is None:
                out.append(text[i:m.end()]); i = m.end(); continue
            nargs, dflt, body = spec
            j, args = m.end(), []
            if dflt is not None:
                o, j2 = opt_at(text, j) if j < len(text) and text[j] == "[" else (None, j)
                args.append(o if o is not None else dflt); j = j2
            need = nargs - len(args)
            ok = True
            for _k in range(need):
                while j < len(text) and text[j] in " \t\n": j += 1
                if j < len(text) and text[j] == "{":
                    a, j = group_at(text, j)
                    if a is None: ok = False; break
                    args.append(a)
                elif j < len(text) and text[j] == "\\":
                    m2 = _CALL.match(text, j)
                    if not m2: ok = False; break
                    args.append(m2.group(0)); j = m2.end()
                elif j < len(text):
                    args.append(text[j]); j += 1
                else: ok = False; break
            if not ok:
                out.append(text[i:m.end()]); i = m.end(); continue
            rep = body
            for k, a in enumerate(args, 1): rep = rep.replace(f"#{k}", a)
            out.append(text[i:m.start()]); out.append(rep)
            i, hit = j, True
            if sum(len(s) for s in out) > limit: break
        out.append(text[i:])
        new = "".join(out)
        if not hit or new == text or len(new) > limit: return new
        text = new
    return text


# ---- de-TeX --------------------------------------------------------------
_DROP_ENV = ("figure", "figure*", "table", "table*", "tikzpicture", "wrapfigure",
             "algorithm", "algorithmic", "thebibliography", "comment")
_ACCENT = {"\\'": "", '\\"': "", "\\`": "", "\\^": "", "\\~": "", "\\=": "", "\\.": ""}
_SIMPLE = [
    (r"\\(label|ref|eqref|cref|Cref|cpageref|autoref|nameref|vref|pageref|hyperref|cite[a-zA-Z]*|footnote|index|nonumber|noindent|qed|qedhere|phantomsection|leavevmode|vspace|hspace|smallskip|medskip|bigskip|centering|item)\s*(\*)?(\[[^\]]*\])?(\{[^{}]*\})?", " "),
    # Font switches and spacing commands, which otherwise land in the text as words.
    (r"\\(xspace|normalfont|normalsize|sffamily|rmfamily|ttfamily|scshape|bfseries|itshape|upshape|mdseries|protect|relax|allowbreak|linebreak|newline|par|small|footnotesize|scriptsize|large|Large|huge|sf|rm|tt|it|bf|sc|em|enspace|thinspace|negthinspace|quad|qquad|hfill|hbox|strut|mathstrut)(?![A-Za-z])", " "),
    (r"\\frac\s*\{([^{}]{0,40})\}\s*\{([^{}]{0,40})\}", r"(\1)/(\2)"),
    (r"\\sqrt\s*\{([^{}]{0,40})\}", r"sqrt(\1)"),
    # Longest first: `text` alone would eat `\textnormal` and leave "normal".
    (r"\\(?:text(?:normal|subscript|superscript|bf|it|sf|tt|sc|rm|up|md)?"
     r"|math(?:rm|sf|bf|bb|cal|it|frak|tt|scr)|emph|operatorname|ensuremath|mbox"
     r"|boldsymbol|bm|pmb|varmathbb|class|cc|complexityclass|prob|problem|lang"
     r"|widetilde|widehat|overline|underline|tilde|hat|bar|vec)\s*\*?\s*", ""),
    (r"\\[\[\]\(\)]", " "),
    (r"\\(left|right|big|Big|bigg|Bigg|displaystyle|limits|,|;|:|!|/)", " "),
    (r"\\\\", " "), (r"[{}$]", " "), (r"~", " "),
]
_GREEK = {"alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε",
          "varepsilon": "ε", "zeta": "ζ", "eta": "η", "theta": "θ", "kappa": "κ",
          "lambda": "λ", "mu": "μ", "nu": "ν", "xi": "ξ", "pi": "π", "rho": "ρ",
          "sigma": "σ", "tau": "τ", "phi": "φ", "varphi": "φ", "chi": "χ",
          "psi": "ψ", "omega": "ω", "Gamma": "Γ", "Delta": "Δ", "Theta": "Θ",
          "Lambda": "Λ", "Pi": "Π", "Sigma": "Σ", "Phi": "Φ", "Psi": "Ψ", "Omega": "Ω"}
_OPS = {"subseteq": "⊆", "subsetneq": "⊊", "subset": "⊂", "supseteq": "⊇", "supset": "⊃",
        "not\\subseteq": "⊄", "nsubseteq": "⊄", "notsubseteq": "⊄", "neq": "≠", "ne": "≠",
        "leq": "≤", "le": "≤", "geq": "≥", "ge": "≥", "ll": "≪", "gg": "≫",
        "cdot": "·", "cdots": "...", "ldots": "...", "dots": "...", "times": "×",
        "in": "∈", "notin": "∉", "cap": "∩", "cup": "∪", "setminus": "\\", "circ": "∘",
        "to": "→", "rightarrow": "→", "Rightarrow": "⇒", "implies": "⇒", "iff": "⟺",
        "leftrightarrow": "↔", "Leftrightarrow": "⟺", "forall": "∀", "exists": "∃",
        "land": "∧", "lor": "∨", "neg": "¬", "lnot": "¬", "approx": "≈", "sim": "~",
        "log": "log", "poly": "poly", "infty": "∞", "sqrt": "sqrt", "bits": "{0,1}",
        "emptyset": "∅", "oplus": "⊕", "otimes": "⊗", "sum": "Σ", "prod": "Π",
        "ell": "ℓ", "mid": "|", "colon": ":", "geqslant": "≥", "leqslant": "≤",
        "langle": "⟨", "rangle": "⟩", "lvert": "|", "rvert": "|", "lVert": "‖", "rVert": "‖",
        "dagger": "†", "ast": "*", "star": "*", "bullet": "·", "wedge": "∧", "vee": "∨",
        "subsetneqq": "⊊", "nsubseteq": "⊄", "equiv": "≡", "propto": "∝", "pm": "±"}


def _first_arg_only(t, name):
    """`\\texorpdfstring{shown}{pdf}` must not contribute both halves to the text."""
    pat, out, i = re.compile(rf"\\{name}\s*(?=\{{)"), [], 0
    while (m := pat.search(t, i)):
        a, j = group_at(t, m.end())
        _, k = group_at(t, j) if j < len(t) and t[j] == "{" else (None, j)
        out.append(t[i:m.start()]); out.append(a or ""); i = k
    out.append(t[i:])
    return "".join(out)


def detex(text, *, limit=4000):
    """Readable plain text. Lossy on purpose — `statement_tex` stays the ground truth."""
    t = _first_arg_only(text, "texorpdfstring")
    for env in _DROP_ENV:
        t = re.sub(rf"\\begin\{{{re.escape(env)}\}}.*?\\end\{{{re.escape(env)}\}}", " ", t, flags=re.S)
    t = re.sub(r"\\not\s*\\subseteq", " ⊄ ", t)
    t = re.sub(r"\\not\s*\\subset", " ⊄ ", t)
    t = re.sub(r"\\not\s*=", " ≠ ", t)
    t = re.sub(r"\\not\s*\\in", " ∉ ", t)
    # `\b` is wrong here: `\Sigma_2` has a word character after the name.
    for k, v in _OPS.items():
        if "\\" in k: continue
        t = re.sub(rf"\\{re.escape(k)}(?![A-Za-z])", f" {v} ", t)
    for k, v in _GREEK.items():
        t = re.sub(rf"\\{k}(?![A-Za-z])", v, t)
    # Escaped braces are content ({0,1}^n), not grouping; hide them from the
    # brace strip below and put them back at the end.
    t = t.replace("\\{", "\x02").replace("\\}", "\x03").replace("\\|", "|")
    t = re.sub(r"\\begin\{[^{}]*\}(\[[^\]]*\])?", " ", t)
    t = re.sub(r"\\end\{[^{}]*\}", " ", t)
    for pat, rep in _SIMPLE: t = re.sub(pat, rep, t)
    t = re.sub(r"\\([A-Za-z@]+)\s*", r"\1 ", t)   # surviving control words: keep the name
    t = t.replace("\x02", "{").replace("\x03", "}")
    t = re.sub(r"\s+", " ", t).strip()
    return t[:limit]


# ---- the canonical pipeline ---------------------------------------------
def normalized_source(blob):
    """blob -> (source_text, files, macros). Deterministic; `verify` re-runs it."""
    files = unpack(blob)
    if not files: return "", {}, {}
    main = main_tex(files)
    if not main: return "", files, {}
    return flatten(files, main), files, collect_macros(files)


def sha256(b): return hashlib.sha256(b if isinstance(b, bytes) else b.encode("utf-8")).hexdigest()


def source_for(aid):
    """{status, src, files, macros, blob_sha256, source_sha256}. Fetches once, then cached."""
    st, blob = fetch_eprint(aid)
    out = {"status": st, "src": "", "files": {}, "macros": {}, "blob_sha256": "", "source_sha256": ""}
    if st != OK or not blob: return out
    out["blob_sha256"] = sha256(blob)
    if blob[:4] == b"%PDF": out["status"] = PDF_ONLY; return out
    src, files, macros = normalized_source(blob)
    out.update(src=src, files=files, macros=macros, source_sha256=sha256(src))
    if not src.strip(): out["status"] = NO_TEX
    return out
