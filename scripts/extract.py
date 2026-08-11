"""Pull the formal content out of a paper's LaTeX source.

What a complexity paper *uses* is not a dataset in the empirical sense — there
are no rows and no measurements. Its examples are formal objects: the problems
it defines, the complexity classes it relates, the bounds it proves, the
hypotheses it assumes. Those live in theorem and definition environments, and
this module lifts them out with byte offsets so every one can be checked back
against the source.

The vocabularies below are *patterns*, exactly like `topic.py`'s regexes — a
list of names to look for, not a claim about any paper. No statement, bound, or
citation is ever written here; everything emitted is a substring of a fetched
source file.
"""
from __future__ import annotations
import re

from fulltext import _first_arg_only, detex, expand, group_at, opt_at

# ---- environments --------------------------------------------------------
_NEWTHM = re.compile(r"\\newtheorem\s*(\*?)\s*\{\s*([^{}]+?)\s*\}")
_DECLTHM = re.compile(r"\\declaretheorem\s*(\[[^\]]*\])?\s*\{\s*([^{}]+?)\s*\}")

# env name -> printed name, for sources that declare nothing (or declare in a
# .sty we did not get). Keys are matched case-insensitively.
DEFAULT_ENVS = {
    "theorem": "Theorem", "thm": "Theorem", "mainthm": "Theorem", "maintheorem": "Theorem",
    "theorem*": "Theorem", "restatable": "Theorem", "namedtheorem": "Theorem",
    "lemma": "Lemma", "lem": "Lemma", "mainlemma": "Lemma", "keylemma": "Lemma",
    "corollary": "Corollary", "cor": "Corollary", "coro": "Corollary",
    "proposition": "Proposition", "prop": "Proposition",
    "definition": "Definition", "defn": "Definition", "defi": "Definition",
    "define": "Definition", "dfn": "Definition", "def": "Definition",
    "claim": "Claim", "clm": "Claim", "fact": "Fact",
    "conjecture": "Conjecture", "conj": "Conjecture",
    "hypothesis": "Hypothesis", "hyp": "Hypothesis", "assumption": "Assumption",
    "question": "Question", "openquestion": "Open Question", "openproblem": "Open Problem",
    "problem": "Problem", "prob": "Problem", "task": "Problem",
    "observation": "Observation", "obs": "Observation",
    "example": "Example", "exa": "Example", "ex": "Example",
    "remark": "Remark", "rem": "Remark", "note": "Remark",
}
# printed name -> kind. Order matters: "open problem" before "problem".
_KINDS = [("open question", "open-question"), ("open problem", "open-question"),
          ("theorem", "theorem"), ("lemma", "lemma"), ("corollar", "corollary"),
          ("propos", "proposition"), ("definition", "definition"), ("defini", "definition"),
          ("conjecture", "conjecture"), ("hypothes", "hypothesis"), ("assumption", "hypothesis"),
          ("question", "open-question"), ("problem", "problem"), ("claim", "claim"),
          ("fact", "fact"), ("observ", "observation"), ("example", "example"),
          ("remark", "remark"), ("note", "remark"), ("notation", "remark")]
KEEP = {"theorem", "lemma", "corollary", "proposition", "definition", "conjecture",
        "hypothesis", "open-question", "problem", "claim", "fact", "observation", "example"}
MAX_BODY = 9000   # anything longer is a mis-parsed environment, not a statement
MIN_BODY = 25


def kind_of(printed):
    p = printed.strip().lower()
    return next((k for pat, k in _KINDS if pat in p), "")


def theorem_envs(files):
    """{env: printed name} from \\newtheorem/\\declaretheorem, plus the defaults."""
    envs = dict(DEFAULT_ENVS)
    for raw in files.values():
        for m in _NEWTHM.finditer(raw):
            env, j = m.group(2), m.end()
            o, j = opt_at(raw, j) if j < len(raw) and raw[j] == "[" else (None, j)
            printed, _ = group_at(raw, j) if j < len(raw) and raw[j] == "{" else (None, j)
            if printed: envs[env.lower()] = re.sub(r"\\[A-Za-z@]+|[{}]", "", printed).strip() or env
        for m in _DECLTHM.finditer(raw):
            opt, env = m.group(1) or "", m.group(2)
            nm = re.search(r"name\s*=\s*([^,\]]+)", opt)
            envs.setdefault(env.lower(), (nm.group(1).strip() if nm else env).strip("{} "))
    return {e: p for e, p in envs.items() if kind_of(p) in KEEP}


def find_envs(src, envs):
    """Every \\begin{env}...\\end{env} span, nesting-aware. Yields dicts with offsets."""
    pat = re.compile(r"\\begin\s*\{\s*(" + "|".join(sorted((re.escape(e) for e in envs), key=len, reverse=True))
                     + r")\s*\}", re.I)
    out, i = [], 0
    while (m := pat.search(src, i)):
        env = m.group(1).lower()
        end_pat = re.compile(r"\\(begin|end)\s*\{\s*" + re.escape(m.group(1)) + r"\s*\}", re.I)
        depth, j, close = 1, m.end(), None
        while (m2 := end_pat.search(src, j)):
            depth += 1 if m2.group(1).lower() == "begin" else -1
            j = m2.end()
            if depth == 0: close = m2; break
        if close is None: i = m.end(); continue
        body_start, body_end = m.end(), close.start()
        head = src[body_start:body_end]
        title, k = (opt_at(head, 0) if head[:1] == "[" else (None, 0))
        # `\begin{restatable}[Title]{proposition}{macroname}` — the real kind is
        # the first argument, and neither argument is part of the statement.
        real = ""
        if env in ("restatable", "restatable*"):
            for _ in range(2):
                while k < len(head) and head[k] in " \t\n": k += 1
                g, k2 = group_at(head, k) if k < len(head) and head[k] == "{" else (None, k)
                if g is None: break
                real, k = (real or g.strip()), k2
        out.append({"env": (real.lower() or env), "title": (title or "").strip(),
                    "start": body_start + k, "end": body_end,
                    "body": src[body_start + k:body_end]})
        i = close.end()
    return out


# ---- vocabularies (patterns, not facts) ----------------------------------
def _canon_key(s):
    """`\\mathsf{S_2E}` and `S_2 E` must land on the same key.

    Case is folded, which is why `_looks_like_class` gates plain-text matches:
    folding alone would let the English word "circuit" match a class named
    CIRCUIT, and "size" match SIZE. It does; that was a live bug.
    """
    s = re.sub(r"\\(math(sf|bf|rm|cal|it|frak|tt)|text(sf|bf|it|tt|rm)?|ensuremath|operatorname|mbox|class|cc|mathmode)\s*\*?", "", s)
    s = s.replace("\\#", "#").replace("\\oplus", "parity").replace("\\Sigma", "sigma")
    s = s.replace("\\Pi", "pi").replace("\\Delta", "delta").replace("\\Theta", "theta")
    s = s.replace("\\mathbb", "").replace("\\!", "").replace("\\,", "").replace("\\;", "")
    s = re.sub(r"\\[A-Za-z@]+", "", s)
    return re.sub(r"[\s{}$^_\-\\]", "", s).lower()


_GREEKW = re.compile(r"\\?(Sigma|Pi|Delta|Theta|Lambda|Gamma)", re.I)


def _looks_like_class(raw):
    """A class name is written in caps. `SIZE` is a class; `size` is a noun.

    Applied only to tokens with no font markup — inside `\\mathsf{...}` the
    author has already told us what it is.
    """
    s = _GREEKW.sub("", raw)
    s = re.sub(r"\^\s*\{?\s*(p|poly|A|O|B|\\ast|\*)\s*\}?", "", s)  # ^p, ^poly, oracle letters
    s = re.sub(r"_\s*\{?[0-9a-z]{1,2}\}?", "", s)                   # the level in \Sigma_k^p
    s = re.sub(r"^co-?", "", s)
    s = re.sub(r"(?i)^(promise|pr|i\.?o\.?|almost|para|samp|f|gap|mod)", "", s)
    letters = re.sub(r"[^A-Za-z]", "", s)
    return letters == "" or letters.isupper()


# Canonical complexity-class names. The key is what `_canon_key` produces.
_CLASS_LIST = [
    "P", "NP", "coNP", "PH", "PSPACE", "NPSPACE", "EXP", "EXPTIME", "NEXP", "NEXPTIME",
    "coNEXP", "EXPSPACE", "NEXPSPACE", "2EXP", "ELEMENTARY",
    "E", "NE", "coNE", "ZPE", "BPE", "MAEXP", "S2E", "S2P", "S2EXP",
    "L", "NL", "coNL", "SL", "RL", "BPL", "ZPL", "polyL", "SC", "SC1", "SC2",
    "LOGSPACE", "NLOGSPACE", "LOGCFL", "TISP",
    "BPP", "RP", "coRP", "ZPP", "PP", "BPPpath", "AlmostP", "promiseBPP", "prBPP", "prP",
    "MA", "AM", "coAM", "IP", "MIP", "MIPstar", "PCP", "SZK", "NISZK", "HVZK", "PZK", "CZK",
    "Sigma2P", "Pi2P", "Delta2P", "Sigma3P", "Pi3P", "Delta3P", "SigmaP", "PiP", "DeltaP",
    "Sigma2E", "Pi2E", "Delta3E", "Sigma3E", "Pi3E", "PSigma2P",
    "sharpP", "parityP", "ModkP", "GapP", "SpanP", "AWPP", "WPP", "PostBQP",
    "UP", "FewP", "SPP", "APX", "PTAS", "FPTAS",
    "AC0", "AC1", "ACC0", "ACC", "TC0", "TC1", "NC0", "NC1", "NC2", "NC", "SAC1", "SAC0",
    "SIZE", "DEPTH", "FORMULA", "Ppoly", "NPpoly",
    "DTIME", "NTIME", "DSPACE", "NSPACE", "ATIME", "ASPACE", "BPTIME",
    "BQP", "QMA", "QMA1", "QCMA", "QIP", "QSZK", "QAM", "QCPH", "StoqMA", "BQL",
    "PDQP", "SampBQP", "SampBPP", "DQC1", "IQP", "QNC", "QAC0", "QP", "EQP",
    "FP", "FNP", "TFNP", "PPAD", "PPADS", "PLS", "PPA", "PPP", "CLS", "EOPL", "UEOPL",
    "PWPP", "FZPP", "FBPP", "FS2P", "NPSV", "APEPP",
    "FPT", "XP", "W1", "W2", "Wt", "WP", "paraNP", "XNLP",
    "VP", "VNP", "VBP", "VF", "VQP", "VNC", "GapL",
]
# Written-out names that carry no font markup. Kept deliberately short: prose
# names for classes are usually the *resource*, not the class — "logspace
# reductions" and "polynomial space bounded" are not claims about L or PSPACE.
_CLASS_TEXT = {
    "polynomial hierarchy": "PH", "polynomial-time hierarchy": "PH",
    "counting hierarchy": "CH", "boolean hierarchy": "BH",
}
# The hierarchies are written with a level that is often a variable, not a digit.
_CLASS_LIST += [f"{g}{i}{s}" for g in ("Sigma", "Pi", "Delta", "Theta")
                for i in ("2", "3", "4", "k", "i", "j", "t") for s in ("P", "E", "EXP")]
_CLASS_LIST += ["BH", "CH", "coUP", "AH", "EXPH", "PSPACEpoly", "EXPpoly", "NEXPpoly", "Wk"]
CLASS_MARKS = {"PCLS": "P", "ECLS": "E", "LCLS": "L"}   # see mark_single_classes
CLASS_CANON = {_canon_key(c): c for c in _CLASS_LIST}
CLASS_CANON.update({_canon_key(k): v for k, v in CLASS_MARKS.items()})
CLASS_CANON.update({_canon_key(k): v for k, v in {
    "#P": "sharpP", "\\#P": "sharpP", "\\oplus P": "parityP", "P/poly": "Ppoly",
    "NP/poly": "NPpoly", "\\Sigma_2^p": "Sigma2P", "\\Sigma_2 P": "Sigma2P",
    "\\Pi_2^p": "Pi2P", "\\Sigma_3^p": "Sigma3P", "\\Pi_3^p": "Pi3P",
    "\\Delta_2^p": "Delta2P", "\\Delta_3^p": "Delta3P", "S_2^p": "S2P", "S_2 E": "S2E",
    "AC^0": "AC0", "TC^0": "TC0", "NC^1": "NC1", "NC^2": "NC2", "ACC^0": "ACC0",
    "W[1]": "W1", "W[2]": "W2", "W[t]": "Wt", "W[P]": "WP", "MIP^*": "MIPstar",
    "coNP": "coNP", "co-NP": "coNP", "co-RP": "coRP", "co-AM": "coAM", "co-NL": "coNL",
    "2-EXP": "2EXP", "EXPTIME": "EXP", "NEXPTIME": "NEXP", "PolyL": "polyL",
}.items()})
# Single letters are classes only inside math font markup; in prose they are words.
_BARE_MIN = 2

# `\ensuremath` is the common one and was missing here; every class inside one
# stayed invisible, which killed most relation matches.
_FONT = re.compile(r"\\(?:math(?:sf|bf|rm|cal|it|frak|tt|bb)|text(?:sf|bf|it|tt|rm|up|sc|normal)?"
                   r"|ensuremath|operatorname\*?|mbox|bm|boldsymbol|underline"
                   r"|class|cc|complexityclass|compclass|comp|cls|mathmode)"
                   r"\s*\*?\s*(?=\{)")
_PLAIN_CLASS = re.compile(
    r"(?<![A-Za-z0-9_])(?:co-?)?(?:NP|PSPACE|PSAPCE|EXPSPACE|NEXPTIME|NEXP|EXPTIME|EXP|BPP|RP|ZPP|BQP|QMA|QCMA|QIP"
    r"|PPAD|PPA|PPP|PLS|TFNP|CLS|FPT|XP|AC0|TC0|NC1|NC2|ACC0|AM|MA|IP|MIP|PCP|SZK|NISZK"
    r"|PH|BPL|NL|SC|VP|VNP|VBP|GapP|SPP|UP|FP|FNP|DTIME|NTIME|DSPACE|NSPACE|SIZE|DEPTH"
    r"|S2E|S2P|ZPE|NEXP|MAEXP|StoqMA|PostBQP|LOGSPACE|LOGCFL|APX|PTAS)"
    r"(?![A-Za-z0-9_])")


# Zero-argument formatting commands. `NP\xspace \subseteq P` reads as a claim
# only once `\xspace` is gone; while it sits there, no relation matches.
_NOARG = re.compile(r"\\(?:xspace|normalfont|sffamily|rmfamily|scshape|bfseries|itshape"
                    r"|protect|allowbreak|relax|displaystyle|limits|nolimits"
                    r"|sf|rm|bf|it|sc|em|quad|qquad|enspace|thinspace|,|;|:|!|\s)")


# Pre-2005 sources declare the font inside the group: `{\rm P}`, not `\mathrm{P}`.
# Those are the papers the backward snowball exists to reach, so this is not a
# nicety — without it their classes are invisible.
_OLDFONT = re.compile(r"\{\s*\\(rm|sf|bf|it|tt|cal|sc|scriptsize|small)\s+([^{}]{1,24}?)\s*\}")
_OLDMAP = {"rm": "mathrm", "sc": "mathrm", "tt": "mathrm", "sf": "mathsf",
           "bf": "mathbf", "it": "mathit", "cal": "mathcal",
           "scriptsize": "mathrm", "small": "mathrm"}


# `W[1]` is one class name split across a bracket; every other class writes its
# parameter as a subscript. Rewritten on the analysis copy only.
_WCLASS = re.compile(r"(?<![A-Za-z0-9])W\s*\[\s*([12tkP])\s*\]")


def normalize_old_fonts(tex, rounds=2):
    for _ in range(rounds):
        new = _OLDFONT.sub(lambda m: f"\\{_OLDMAP[m.group(1)]}{{{m.group(2)}}}", tex)
        if new == tex: break
        tex = new
    return _WCLASS.sub(lambda m: f"W{m.group(1)}", tex)


def unwrap_fonts(tex):
    """Drop math-font wrappers but keep their contents. Formatting noise goes too."""
    tex = _NOARG.sub(" ", _first_arg_only(tex, "texorpdfstring"))
    out, i = [], 0
    while (m := _FONT.search(tex, i)):
        body, end = group_at(tex, m.end())
        if body is None: out.append(tex[i:m.end()]); i = m.end(); continue
        out.append(tex[i:m.start()]); out.append(unwrap_fonts(body)); i = end
    out.append(tex[i:])
    return "".join(out)


# Fonts an author uses for a complexity class. `\mathcal` and `\mathbb` are for
# sets and fields — `\mathcal{P}` is a powerset, not polynomial time.
_CLASS_FONT = re.compile(r"\\(?:mathsf|mathbf|mathrm|textsf|textbf|texttt|mathtt|operatorname"
                         r"|class|cc|complexityclass|compclass|cls)\b")
# Control words a class name may legitimately still contain once fonts are gone.
_UNEXPANDED = re.compile(r"\\(?!Sigma|Pi|Delta|Theta|#|oplus|,|;|!|:|\s)[A-Za-z@]+")


def _font_tokens(tex):
    """(content, start, end) for every font-wrapped group."""
    for m in _FONT.finditer(tex):
        body, end = group_at(tex, m.end())
        if body is None: continue
        yield body, m.start(), end


def _class_font_tokens(tex):
    """As above, but only the fonts that name classes, and remembering which."""
    for m in _FONT.finditer(tex):
        body, end = group_at(tex, m.end())
        if body is None: continue
        yield body, m.start(), end, bool(_CLASS_FONT.match(m.group(0)))


_ORACLE = re.compile(r"^\s*\^\s*\{?\s*$")
# `S_2E`, `\Sigma_2^p`, `AC^0`, `\#P`: a name, an optional subscript, more
# letters, an optional superscript. Anchored so `NPC` never reads as `NP`.
_TOKEN = re.compile(r"(?<![A-Za-z0-9_])(?:\\#|#|\\oplus\s*)?\\?[A-Za-z][A-Za-z0-9]*"
                    r"(?:_\s*\{?[0-9kt]\}?)?[A-Za-z0-9]*"
                    r"(?:\^\s*\{?[a-zA-Z0-9*]{1,4}\}?)?")


_UNKNOWN_OK = re.compile(r"^[A-Z][A-Za-z0-9]{2,15}$")


def class_spans(sym, *, unknown=False):
    """(canonical, start, end, known) for class tokens in *unwrapped* text.

    `ZPE^{NP}` is one class, not two. Single letters (`P`, `E`, `L`) are only
    recognized when the caller kept their font markup — see `classes_in`.

    With `unknown=True`, class-shaped names outside the vocabulary are returned
    too, flagged `known=False`. Papers define their own classes constantly — a
    closed vocabulary would drop every relation a paper proves about its own.
    """
    hits = []
    for m in _TOKEN.finditer(sym):
        head = re.split(r"[\[\(]", m.group(0), 1)[0]
        # Count letters, not characters: `L^2(G)` is a function space, and its
        # exponent must not be what makes the name long enough to be a class.
        if len(re.sub(r"[^A-Za-z]", "", head)) < _BARE_MIN and not head.lstrip().startswith(("#", "\\#", "\\oplus")):
            continue
        if not _looks_like_class(head): continue
        c, kn = CLASS_CANON.get(_canon_key(head)), True
        if not c:  # `ZPE^{NP}`, `SIZE^A`: the base names the class, the exponent is an oracle
            base, _, sup = head.partition("^")
            if (c := CLASS_CANON.get(_canon_key(base))):
                if (o := CLASS_CANON.get(_canon_key(sup))): c = f"{c}^{o}"
            elif unknown and _UNKNOWN_OK.match(base.strip("\\")): c, kn = base.strip("\\"), False
            else: continue
        hits.append([c, m.start(), m.end(), kn])
    out = []
    for h in hits:
        if out and out[-1][3] and h[3] and _ORACLE.match(sym[out[-1][2]:h[1]]):
            prev = out[-1]
            prev[0], prev[2] = f"{prev[0]}^{h[0]}", h[2] + (1 if sym[h[2]:h[2] + 1] == "}" else 0)
            continue
        out.append(h)
    return [tuple(h) for h in out]


def classes_in(tex):
    """Canonical class names in a fragment, with spans where known.

    Two passes on purpose: font-wrapped tokens may be single letters (`P`, `L`,
    `E`), plain-text ones may not — `\\bP\\b` matches ordinary prose.
    """
    tex = normalize_old_fonts(tex)
    hits = []
    for body, s, e, class_font in _class_font_tokens(tex):
        inner = unwrap_fonts(body)
        # `SIZE[2^n/n]`, `DTIME(t(n))`: the head names the class.
        head = re.split(r"[\[\(]", inner, 1)[0]
        # A one-letter name is a class only when the author set it in a class
        # font; `\mathcal{E}` is a set of events in half the papers in the field.
        short = len(re.sub(r"[^A-Za-z0-9#]", "", head)) < _BARE_MIN
        if short and not class_font: continue
        # `\mathrm{e}^{-100}` is Euler's number. Case is folded downstream, so a
        # one-letter name has to be capitalized here or it is not a class.
        if short and head.strip().islower(): continue
        # `L^2(R)`, `E^3`: a one-letter name with a numeric exponent is a norm
        # or a space. Classes written that way (`AC^0`, `NC^1`) are longer.
        if short and re.match(r"\s*\^\s*\{?\s*\d", tex[e:]): continue
        # `QIP\textsubscript{U}\mathsf{L}` is one name the paper coined, not a
        # containment involving L: a class does not start mid-word.
        if short and tex[:s].rstrip().endswith(("}", "_")): continue
        # Blackboard bold is for number sets, probability and expectation —
        # `\mathrm{\mathbb{E}}` is still an expectation, whatever wraps it.
        if "\\mathbb" in body: continue
        # A macro we could not expand may be anything. `_canon_key` deletes
        # unknown control words, so `\mathrm{\bm{\newmathbb{E}}}` would read as
        # the class E; only the names a class is actually written with pass.
        if _UNEXPANDED.search(unwrap_fonts(body)): continue
        # `\mathsf{W}[1]` is the parameterized class, spelled across a bracket.
        if (w := re.match(r"\s*\[\s*([12tkP])\s*\]", tex[e:])) and head.strip() == "W":
            hits.append((f"W{w.group(1)}", s, e + w.end())); continue
        # `\E[X]`, `\P(A)`: expectation and probability, not E and P. No class
        # with a one-letter name takes an argument.
        if short and re.match(r"\s*(?:\\(?:left|big|Big|bigg|Bigg)l?)?\s*[\[\(]", tex[e:]): continue
        if (c := CLASS_CANON.get(_canon_key(head))): hits.append((c, s, e))
    sym = unwrap_fonts(tex)
    for c, _, _, _ in class_spans(sym):
        hits.append((c, -1, -1))
        if "^" in c: hits += [(p, -1, -1) for p in c.split("^")]  # keep the parts findable
    low = sym.lower()
    for phrase, c in _CLASS_TEXT.items():
        if phrase in low: hits.append((c, -1, -1))
    return hits


# Named computational problems: what the authors actually compute on.
PROBLEM_PATTERNS = {
    "SAT": r"\b(?:the )?satisfiability problem\b|\bCNF-?SAT\b|(?<![A-Za-z0-9-])SAT(?![A-Za-z0-9])",
    "3SAT": r"\b3-?SAT\b|\b3-?CNF-?SAT\b",
    "k-SAT": r"\bk-?SAT\b|\bk-?CNF-?SAT\b",
    "MAX-SAT": r"\bmax-?\d?-?sat\b",
    "QBF/TQBF": r"\bTQBF\b|\bQBF\b|quantified boolean formula",
    "Clique": r"\b(?:max(?:imum)?[- ])?clique problem\b|\bk-?clique\b|\bmaximum clique\b",
    "Independent Set": r"\b(?:maximum )?independent set\b",
    "Vertex Cover": r"\bvertex cover\b",
    "Dominating Set": r"\bdominating set\b",
    "Set Cover": r"\bset cover\b",
    "Hitting Set": r"\bhitting set\b",
    "Graph Coloring": r"\bgraph colou?ring\b|\bk-?colou?rability\b|\bchromatic number\b",
    "Subset Sum": r"\bsubset[- ]sum\b",
    "Knapsack": r"\bknapsack\b",
    "TSP": r"\btravel(?:l)?ing salesman\b|\bTSP\b",
    "Hamiltonian Path/Cycle": r"\bhamiltonian (?:path|cycle|circuit)\b",
    "Graph Isomorphism": r"\bgraph isomorphism\b|\bGI problem\b",
    "Group Isomorphism": r"\bgroup isomorphism\b",
    "Reachability/STCON": r"\bs-?t[- ]connectivity\b|\bSTCON\b|\bdirected (?:s-?t )?reachability\b|\bgraph reachability\b",
    "Tree Evaluation": r"\btree evaluation\b",
    "Edit Distance": r"\bedit distance\b|\blevenshtein\b",
    "LCS": r"\blongest common subsequence\b|\bLCS\b",
    "APSP": r"\ball[- ]pairs shortest paths?\b|\bAPSP\b",
    "3SUM": r"\b3-?SUM\b",
    "Orthogonal Vectors": r"\borthogonal vectors?\b|\bOV problem\b|\bOVC\b",
    "Diameter": r"\bgraph diameter\b|\bdiameter problem\b",
    "Matrix Multiplication": r"\bmatrix multiplication\b|\bboolean matrix multiplication\b|\bBMM\b",
    "Permanent": r"\bpermanent\b",
    "Determinant": r"\bdeterminant\b",
    "PIT": r"\bpolynomial identity testing\b|\bPIT\b",
    "MCSP": r"\bminimum circuit size problem\b|\bMCSP\b",
    "MKTP": r"\bMKTP\b|\bminimum (?:KT|time-bounded Kolmogorov)\b",
    "Kolmogorov Complexity": r"\bkolmogorov complexity\b|\bK\^?\{?poly\}?\b|\bMINKT\b",
    "Range Avoidance": r"\brange avoidance\b|\bAvoid problem\b|\bremote point\b",
    "Parity": r"\bthe parity function\b|\bPARITY\b",
    "Majority": r"\bmajority function\b|\bMAJORITY\b|\bMAJ\b",
    "Inner Product": r"\binner[- ]product function\b|\bIP function\b",
    "Set Disjointness": r"\bset disjointness\b|\bdisjointness (?:problem|function)\b|\bDISJ\b",
    "Equality": r"\bequality function\b|\bEQ function\b",
    "Gap-Hamming": r"\bgap[- ]hamming\b",
    "Index": r"\bindex(?:ing)? (?:problem|function)\b",
    "Pointer Chasing": r"\bpointer (?:chasing|jumping)\b",
    "Karchmer-Wigderson": r"\bkarchmer-?wigderson\b",
    "Unique Games": r"\bunique games?\b",
    "Label Cover": r"\blabel cover\b",
    "Max-Cut": r"\bmax-?cut\b",
    "Vertex Expansion/SSE": r"\bsmall[- ]set expansion\b",
    "CSP": r"\bconstraint satisfaction\b|\bCSPs?\b",
    "Nash Equilibrium": r"\bnash equilibrium\b",
    "Local Search": r"\blocal search problem\b",
    "Pigeonhole": r"\bpigeonhole principle\b|\bPHP\b",
    "Local Hamiltonian": r"\blocal hamiltonian\b",
    "Quantum Circuit Sampling": r"\brandom circuit sampling\b|\bboson sampling\b",
    "Forrelation": r"\bforrelation\b",
    "Simon/Bernstein-Vazirani": r"\bsimon'?s problem\b|\bbernstein-?vazirani\b",
    "Factoring/Discrete Log": r"\binteger factoring\b|\bfactoring problem\b|\bdiscrete logarithm\b",
    "SVP/CVP": r"\bshortest vector problem\b|\bclosest vector problem\b|\bSVP\b|\bCVP\b",
    "Learning Parity with Noise": r"\blearning parity with noise\b|\bLPN\b|\bLWE\b",
    "Planted Clique": r"\bplanted clique\b|\bhidden clique\b",
    "Random k-SAT Refutation": r"\brefut(?:ing|ation of) random\b|\brandom k-?SAT\b",
    "Matching": r"\bperfect matching\b|\bbipartite matching\b",
    "Max-Flow": r"\bmaximum flow\b|\bmax-?flow\b",
    "Sorting/Selection": r"\bsorting (?:problem|lower bound)\b|\bselection problem\b",
    "Counting Solutions": r"\bcounting (?:satisfying assignments|solutions)\b|\b#SAT\b|\b#CSP\b",
    "Partition Function": r"\bpartition function\b|\bholant\b|\bising model\b",
    "Circuit Evaluation": r"\bcircuit (?:value|evaluation) problem\b|\bCVP problem\b",
    "Word Problem": r"\bword problem\b",
    "Model Checking": r"\bmodel[- ]checking\b",
    "Sensitivity/Block Sensitivity": r"\bblock sensitivity\b|\bsensitivity conjecture\b",
    "Collision/Element Distinctness": r"\belement distinctness\b|\bcollision problem\b",
    "Search/Grover": r"\bunstructured search\b|\bgrover'?s\b|\bOR function\b",
    "Nisan-Wigderson": r"\bnisan-?wigderson\b",
    "Ramsey Graph": r"\bramsey graph\b",
    "Rigid Matrix": r"\brigid matri(?:x|ces)\b|\bmatrix rigidity\b",
    "Two-Source Extractor": r"\btwo-?source extractor\b",
    "Error-Correcting Code": r"\blinear codes?\b|\berror[- ]correcting code\b|\blocally decodable code\b|\bLDC\b",
    "Sunflower": r"\bsunflower (?:lemma|conjecture)\b",
}
PROBLEM_RE = {k: re.compile(v, re.I) for k, v in PROBLEM_PATTERNS.items()}

# Hardness assumptions a statement may be conditioned on.
HYPOTHESIS_PATTERNS = {
    "SETH": r"\bSETH\b|\bstrong exponential[- ]time hypothesis\b",
    "ETH": r"(?<!S)(?<!N)\bETH\b|\bexponential[- ]time hypothesis\b",
    "NSETH": r"\bNSETH\b|\bnondeterministic SETH\b",
    "OV Conjecture": r"\borthogonal vectors conjecture\b|\bOV conjecture\b|\bOVC\b",
    "3SUM Conjecture": r"\b3-?SUM (?:conjecture|hypothesis)\b",
    "APSP Conjecture": r"\bAPSP (?:conjecture|hypothesis)\b",
    "k-Clique Hypothesis": r"\bk-?clique (?:conjecture|hypothesis)\b",
    "Unique Games Conjecture": r"\bunique games conjecture\b|\bUGC\b",
    "P != NP": r"\bP\s*(?:\\ne|\\neq|≠|!=)\s*NP\b|\bP\s*(?:vs\.?|versus)\s*NP\b|\bP\s*=\s*NP\b",
    "PH does not collapse": r"\b(?:polynomial hierarchy|PH) (?:does not collapse|is infinite)\b|\bPH\b.{0,20}\binfinite\b",
    "One-Way Functions Exist": r"\bone-?way functions? exist\b|\bexistence of one-?way functions\b",
    "Cryptographic Assumptions": r"\bLWE assumption\b|\bhardness of LWE\b|\bfactoring is hard\b|\bindistinguishability obfuscation\b|\biO\b",
    "Log-Rank Conjecture": r"\blog-?rank conjecture\b",
    "Sensitivity Conjecture": r"\bsensitivity conjecture\b",
    "Permanent vs Determinant": r"\bpermanent (?:vs\.?|versus) determinant\b|\bValiant'?s (?:conjecture|hypothesis)\b|\bVP\s*(?:\\ne|\\neq|≠)\s*VNP\b",
    "NEXP not in P/poly": r"\bNEXP\b.{0,30}\bP/poly\b",
    "Rich Verifier / Gap-ETH": r"\bgap-?ETH\b",
    "Random Oracle / Relativization": r"\brelativi[sz]ing\b|\brelative to (?:a|an) (?:random )?oracle\b",
}
HYPOTHESIS_RE = {k: re.compile(v, re.I) for k, v in HYPOTHESIS_PATTERNS.items()}

# ---- relations and bounds ------------------------------------------------
_RELS = [(r"\\not\s*\\subseteq|\\nsubseteq|\\not\s*\\subset|\\nsubset|⊄", "not-contained-in"),
         (r"\\subsetneq|\\subsetneqq|⊊", "strictly-contained-in"),
         (r"\\subseteq|\\subset|⊆|⊂", "contained-in"),
         (r"\\supseteq|\\supset|⊇|⊃", "contains"),
         (r"\\neq|\\ne\b|\\not\s*=|≠", "separated-from"),
         (r"=", "equals")]
_REL_RE = [(re.compile(r"^\s*(?:" + p + r")\s*$"), n) for p, n in _RELS]
_ARG = re.compile(r"^\s*(\[[^\[\]]{0,60}\]|\([^()]{0,60}\))")

_BOUND_HEADS = r"\\?(?:tilde|widetilde|overline)?\s*\{?\s*(O|o|Omega|omega|Theta|theta|poly|polylog|exp|quasipoly)\s*\}?"
_BOUND = re.compile(r"\\(?:tilde|widetilde)\s*\{?\s*\\?(?:O|Omega|Theta)\s*\}?\s*[\(\{]"
                    r"|\\(?:Omega|Theta|omega)\s*[\(\{]"
                    r"|(?<![A-Za-z\\])(?:O|o|poly|polylog|exp)\s*[\(\{]")
# `q` and `d` are dropped: `\mathbb{F}_q^{d \times n}` is a matrix shape, not a
# running time, and it is everywhere in the algebraic and coding papers.
_POWER = re.compile(r"(?<![A-Za-z\\])(?:2|n|N|m|s|t|k)\s*\^\s*(\{[^{}]{1,60}\}|[A-Za-z0-9]+)")


def _balanced(text, i):
    """Read (...) or {...} at text[i]; returns (span_text, end)."""
    if i >= len(text): return None, i
    op = text[i]
    cl = {"(": ")", "{": "}", "[": "]"}.get(op)
    if cl is None: return None, i
    depth, j = 0, i
    while j < len(text):
        c = text[j]
        if c == "\\": j += 2; continue
        if c == op: depth += 1
        elif c == cl:
            depth -= 1
            if depth == 0: return text[i:j + 1], j + 1
        j += 1
    return None, i


_SETOP = re.compile(r"^\s*(\\cap|\\cup|∩|∪|\\times|×|\\oplus|\\circ|/)\s*$")
_SETSYM = {"\\cap": "∩", "\\cup": "∪", "\\times": "×", "\\oplus": "⊕", "\\circ": "∘"}
# `S_2E \not\subset i.o.-SIZE[2^n/n]`: the modifier is part of the claim, so it
# is recorded rather than dropped, and it must not block the relation match.
_MODIFIER = re.compile(r"(i\.?\s*o\.?|a\.?\s*e\.?|infinitely often|almost everywhere|almost all)[-\s.]*", re.I)
_SPACING = re.compile(r"\\(?:[,;:!]|quad|qquad|;|\s)|~|\\ensuremath|\{|\}|\$")


def _strip_scripts(gap):
    """Drop leading sub/superscripts and bracket arguments: `^1[c,s]` before a `\\cup`."""
    for _ in range(3):
        if (s := _SUP.match(gap)): gap = gap[s.end():]; continue
        if (a := _ARG.match(gap)): gap = gap[a.end():]; continue
        break
    return gap


_SINGLE = {"P": "PCLS", "E": "ECLS", "L": "LCLS"}
_UNMARK = re.compile("|".join(_SINGLE.values()))


def mark_single_classes(tex):
    """`\\mathsf{P}` -> `PCLS`, so a one-letter class survives font stripping.

    Relations are matched on unwrapped text, where `\\mathsf{P}` and the letter
    P are indistinguishable — and a bare P must not count. Marking keeps
    `L \\subseteq NL \\subseteq P` matchable without letting prose in.
    """
    out, i = [], 0
    for m in _FONT.finditer(tex):
        if m.start() < i: continue
        body, end = group_at(tex, m.end())
        if body is None: continue
        inner = re.sub(r"[\s{}$]", "", unwrap_fonts(body))
        if _CLASS_FONT.match(m.group(0)) and inner in _SINGLE and "\\mathbb" not in body:
            out.append(tex[i:m.start()]); out.append(_SINGLE[inner]); i = end
    out.append(tex[i:])
    return "".join(out)


def _unmark(s): return _UNMARK.sub(lambda m: m.group(0)[0], s)


def _operands(sym):
    """Merge class spans joined by ∩/∪/× into one operand, so `A ∩ B ⊄ C` stays whole.

    Losing the second half of an intersection would not weaken the claim, it
    would change it: `A ∩ B ⊆ C` does not give `B ⊆ C`.
    """
    ops = []
    for c, s, e, kn in class_spans(sym, unknown=True):
        m = _SETOP.match(_strip_scripts(sym[ops[-1]["end"]:s])) if ops else None
        if m:
            ops[-1]["classes"].append(c); ops[-1]["end"] = e; ops[-1]["known"] &= kn
            ops[-1]["joins"].append(_SETSYM.get(m.group(1), m.group(1)))
        else:
            ops.append({"classes": [c], "start": s, "end": e, "known": kn, "joins": []})
    for o in ops:
        o["tex"] = re.sub(r"\s+", " ", sym[o["start"]:o["end"]]).strip()
        o["name"] = o["classes"][0] + "".join(f" {j} {c}" for j, c in zip(o["joins"], o["classes"][1:]))
    return ops


_SUP = re.compile(r"^\s*[\^_]\s*(\{[^{}]{0,30}\}|[A-Za-z0-9*']{1,8})")


def _clean_gap(gap):
    """Strip sub/superscripts, an argument, spacing and an i.o./a.e. modifier.

    `QIPL_m[c,s] \\subseteq P` must reduce to the relation symbol alone.
    """
    arg = ""
    for _ in range(3):                       # sub, sup and argument in any order
        if (s := _SUP.match(gap)): gap = gap[s.end():]; continue
        if (a := _ARG.match(gap)): arg, gap = arg or a.group(1).strip(), gap[a.end():]; continue
        break
    gap = _SPACING.sub(" ", gap)
    mod = ""
    if (m := _MODIFIER.search(gap)):
        mod = re.sub(r"[\s.]", "", m.group(1)).lower(); gap = gap[:m.start()] + " " + gap[m.end():]
    return gap.strip(" -"), arg, mod


def relations_in(tex):
    """Class-vs-class claims: (lhs, relation, rhs) with the verbatim fragment.

    Two class operands separated by nothing but a relation symbol. The claim is
    the paper's, not ours; we only record where it sits in the source.
    """
    sym, out = unwrap_fonts(mark_single_classes(normalize_old_fonts(tex))), []
    ops = _operands(sym)
    for a, b in zip(ops, ops[1:]):
        # Both sides unknown is almost always two ordinary symbols, not a claim.
        if not (a["known"] or b["known"]): continue
        gap, larg, lmod = _clean_gap(sym[a["end"]:b["start"]])
        rel = next((n for p, n in _REL_RE if p.match(gap)), "")
        if not rel: continue
        rarg = _ARG.match(sym[b["end"]:])
        end = b["end"] + (rarg.end() if rarg else 0)
        out.append({"lhs": a["name"], "lhs_classes": a["classes"], "lhs_arg": larg,
                    "lhs_known": a["known"], "relation": rel, "modifier": lmod,
                    "rhs": b["name"], "rhs_classes": b["classes"], "rhs_known": b["known"],
                    "rhs_arg": (rarg.group(1).strip() if rarg else ""),
                    "tex": _unmark(re.sub(r"\s+", " ", sym[a["start"]:end]).strip())})
    return out


_RESOURCE = re.compile(r"(?<![A-Za-z])(SIZE|DEPTH|FORMULA|DTIME|NTIME|TIME|DSPACE|NSPACE|SPACE"
                       r"|ATIME|BPTIME|SIZEDEPTH)\s*[\[\(]")


def bounds_in(tex):
    """Asymptotic expressions, verbatim: `2^{n/2}`, `\\Omega(n\\log n)`, `SIZE[2^n/n]`."""
    sym, out = unwrap_fonts(normalize_old_fonts(tex)), []
    for m in _RESOURCE.finditer(sym):
        arg, _ = _balanced(sym, m.end() - 1)
        if arg and len(arg) <= 80: out.append(re.sub(r"\s+", " ", m.group(1) + arg).strip())
    for m in _BOUND.finditer(sym):
        arg, end = _balanced(sym, m.end() - 1)
        if arg is None or len(arg) > 80: continue
        out.append(re.sub(r"\s+", " ", (sym[m.start():m.end() - 1] + arg)).strip())
    for m in _POWER.finditer(sym):
        out.append(re.sub(r"\s+", " ", m.group(0)).strip())
    seen, uniq = set(), []
    for b in out:
        k = re.sub(r"[\s{}\\]", "", b)
        if k not in seen: seen.add(k); uniq.append(b)
    return uniq[:24]


# ---- assembly ------------------------------------------------------------
_LABEL = re.compile(r"\\label\s*\{([^{}]+)\}")
# Two shapes of problem statement: the tabular one ("Input: ... Output: ...")
# and the prose one ("given a circuit C, find a string outside its image").
_SPEC_FIELDS = (re.compile(r"\b(input|instance)\b\s*(?:[:.]|is\b|consists\b)", re.I),
                re.compile(r"\b(output|question|goal|task|decide|find)\b\s*[:.]"
                           r"|\bYES\b.{0,300}\bNO\b", re.I | re.S))
_SPEC_PROSE = re.compile(r"\b(?:given|on input|takes as input)\b.{0,400}?"
                         r"\b(find|decide|determine|compute|output|return|count|distinguish)\b", re.I | re.S)


# Problems the authors name in math font rather than in prose: `\cc{Avoid}`,
# `\prob{MCSP}`. Case-sensitive on purpose — "avoid" is also an English verb.
PROBLEM_TOKENS = {
    "Avoid": "Range Avoidance", "SAT": "SAT", "3SAT": "3SAT", "3-SAT": "3SAT",
    "kSAT": "k-SAT", "CNFSAT": "SAT", "MCSP": "MCSP", "MKTP": "MKTP", "MINKT": "MKTP",
    "PIT": "PIT", "DISJ": "Set Disjointness", "Disj": "Set Disjointness",
    "PARITY": "Parity", "Parity": "Parity", "MAJ": "Majority", "MAJORITY": "Majority",
    "OV": "Orthogonal Vectors", "APSP": "APSP", "3SUM": "3SUM", "EditDistance": "Edit Distance",
    "LCS": "LCS", "TQBF": "QBF/TQBF", "QBF": "QBF/TQBF", "GI": "Graph Isomorphism",
    "Clique": "Clique", "CLIQUE": "Clique", "VertexCover": "Vertex Cover",
    "SetCover": "Set Cover", "IndSet": "Independent Set", "TSP": "TSP",
    "PHP": "Pigeonhole", "Perm": "Permanent", "Det": "Determinant",
    "STCONN": "Reachability/STCON", "STCON": "Reachability/STCON", "Reach": "Reachability/STCON",
    "TreeEval": "Tree Evaluation", "Forrelation": "Forrelation", "IP": "Inner Product",
}


# Query and communication complexity state their results in measures applied to
# a function, not in class names: `R(f) = \Omega(Q(f)^2)`. Anchored on the
# argument so a stray `s(n)` or `C` does not count.
_MEASURE = re.compile(r"(?<![A-Za-z0-9_\\])(R_0|R_1|R|Q_E|Q_0|Q|D|deg|adeg|bs|fbs|s|C|UC|N|UN"
                      r"|IC|CC|disc|corr|rank|gamma_2|lambda|adv|ADV)"
                      r"\s*(?:[_^]\s*\{?[A-Za-z0-9,\\+\-*]{0,10}\}?)?\s*\(\s*\\?[fFgGh](?![A-Za-z0-9])")


def measures_in(tex):
    """Complexity measures the statement is about: R, Q, D, deg, bs, IC …"""
    sym = unwrap_fonts(normalize_old_fonts(tex))
    return sorted({m.group(1) for m in _MEASURE.finditer(sym)})


def terms_in(text, tex=""):
    """Named problems and hypotheses mentioned. Text is the de-TeXed form."""
    hay = text + " " + tex
    probs = {k for k, p in PROBLEM_RE.items() if p.search(hay)}
    for body, _, _ in _font_tokens(tex):
        tok = re.sub(r"[\s{}$\\]", "", unwrap_fonts(body))
        # `IP` is also a class; only take it when the fragment reads as a function.
        if tok == "IP" and "function" not in text.lower(): continue
        if (p := PROBLEM_TOKENS.get(tok)): probs.add(p)
    return (sorted(probs), sorted(k for k, p in HYPOTHESIS_RE.items() if p.search(hay)))


# A closed vocabulary cannot name what it has not met. These two catch the rest:
# objects the paper sets in math font (`\cc{Avoid}`, `\prob{MissingString}`) and
# noun phrases it calls a problem.
_STOPOBJ = re.compile(
    r"^(?:the|a|an|for|and|or|if|then|let|we|this|that|there|here|it|its"
    r"|boolean|input|output|instance|given|yes|no|case|cases|proof|note|remark"
    r"|theorem|lemma|definition|corollary|proposition|claim|fact|observation|example"
    r"|algorithm|figure|table|section|appendix|equation|part|step|round|phase"
    r"|moreover|since|thus|hence|first|second|third|finally|suppose|assume|fix"
    r"|recall|indeed|namely|consider|observe|conversely|otherwise|similarly"
    r"|furthermore|therefore|however|before|after|when|where|while|with|without)$", re.I)
_NAMED_PROBLEM = re.compile(r"\b((?:[A-Z][A-Za-z0-9-]*(?:\s+[a-z]{1,4})?\s+){0,3}[A-Z][A-Za-z0-9-]*)"
                            r"\s+(?:problem|conjecture|hypothesis|function)\b")


def named_objects(text, tex=""):
    """Free-form object names, so the closed vocabulary is not the ceiling."""
    out = set()
    for body, _, _ in _font_tokens(tex):
        tok = re.sub(r"[\s{}$]", "", unwrap_fonts(body))
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9\-']{2,24}", tok): continue
        if CLASS_CANON.get(_canon_key(tok)) or _STOPOBJ.match(tok): continue
        if tok.islower(): continue          # a word set in italics is emphasis
        out.add(tok)
    for m in _NAMED_PROBLEM.finditer(text):
        nm = m.group(1).strip()
        if len(nm) > 2 and not _STOPOBJ.match(nm.split()[0]): out.add(nm)
    return sorted(out)[:12]


def is_problem_spec(text, kind):
    """A definition that names an input and a task is a problem the paper computes on."""
    if kind not in ("definition", "problem"): return False
    return bool((_SPEC_FIELDS[0].search(text) and _SPEC_FIELDS[1].search(text))
                or _SPEC_PROSE.search(text))


def extract(src, files, macros, envs=None):
    """Source text -> list of example dicts. Offsets index `src` exactly."""
    envs = envs if envs is not None else theorem_envs(files)
    doc = src
    if (b := doc.find("\\begin{document}")) >= 0: base = b
    else: base = 0
    out = []
    for n, e in enumerate(find_envs(doc[base:], envs), 1):
        body = e["body"]
        if not (MIN_BODY <= len(body) <= MAX_BODY): continue
        kind = kind_of(envs.get(e["env"], e["env"]))
        if kind not in KEEP: continue
        exp = normalize_old_fonts(expand(body, macros))
        text = detex(exp)
        if len(text) < MIN_BODY: continue
        labels = _LABEL.findall(body)
        classes = sorted({c for c, _, _ in classes_in(exp)})
        problems, hyps = terms_in(text, exp)
        out.append({
            "ordinal": n, "kind": kind, "env": e["env"],
            "printed_name": envs.get(e["env"], ""), "title": detex(expand(e["title"], macros), limit=200),
            "label": labels[0] if labels else "",
            "statement_tex": body, "statement_text": text,
            "char_start": base + e["start"], "char_end": base + e["end"],
            "classes": classes, "problems": problems, "hypotheses": hyps,
            "measures": measures_in(exp), "named_objects": named_objects(text, exp),
            "relations": relations_in(exp), "bounds": bounds_in(exp),
            "problem_spec": is_problem_spec(text, kind),
        })
    return out


def paper_terms(src, macros):
    """Whole-document usage counts: which classes and problems this paper works with."""
    body = src[src.find("\\begin{document}"):] if "\\begin{document}" in src else src
    body = body[:400_000]
    exp = normalize_old_fonts(expand(body, macros, rounds=3, limit=1_200_000))
    text = detex(exp, limit=400_000)
    from collections import Counter
    cc = Counter(c for c, _, _ in classes_in(exp))
    pc = Counter(k for k, p in PROBLEM_RE.items() for _ in p.finditer(text))
    hc = Counter(k for k, p in HYPOTHESIS_RE.items() for _ in p.finditer(text))
    return ({k: v for k, v in cc.most_common(40)}, {k: v for k, v in pc.most_common(40)},
            {k: v for k, v in hc.most_common(20)})
