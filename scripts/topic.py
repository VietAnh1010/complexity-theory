"""Topic-specific vocabulary for this dataset.

Everything that encodes *what we are mining* lives here rather than in
common.py, so the subject can be retuned without touching the pipeline. Used
for three things: gating snowball expansion, auto-tagging subareas, and giving
the screening step a cheap prior.

Two rules shaped these patterns:

  recall first   the gate only has to avoid throwing away complexity theory;
                 the arXiv category filter and screening both narrow afterwards
  no bare class letters
                 `\\bP\\b` and `\\bL\\b` match ordinary prose in every paper ever
                 written. Single-letter classes appear only inside a longer
                 phrase ("P vs NP", "L = SL"), never on their own.
"""

from __future__ import annotations

import re

from common import clean_text

# --------------------------------------------------------------------------
# Is this a complexity theory paper at all?
# --------------------------------------------------------------------------

# Three families, any one of which is enough: named complexity classes, the
# vocabulary of hardness and bounds, and the named resources being measured.
COMPLEXITY_TERMS = re.compile(
    r"\b("
    # -- named classes. Multi-letter only; see the module docstring.
    r"NP|coNP|PSPACE|NPSPACE|EXPTIME|EXPSPACE|NEXP|EEXP|BPP|RP|ZPP|BPL|RL"
    r"|PPAD|PPAD?P|PLS|TFNP|PPA|PPP|CLS|FNP|FPT|XP"
    r"|AC0|AC\^0|TC0|TC\^0|NC1|NC\^1|NC2|ACC0|ACC\^0"
    r"|BQP|QMA|QCMA|QIP|QSZK|StoqMA"
    r"|SZK|NISZK|MA|AM|IP|MIP|PCP|PH|UP|SPP"
    r"|DTIME|NTIME|DSPACE|NSPACE|SIZE|DEPTH"
    r"|VP|VNP|VBP|VF"
    r")\b"
    # -- these need the context of a longer phrase, not a bare letter.
    r"|\bP\s*(vs\.?|versus|=|≠|!=|\\neq)\s*NP\b"
    r"|\b(#|sharp[- ])P\b|\bpolynomial hierarchy\b|\bcomplexity class(es)?\b"
    r"|\b(log|logarithmic)[- ]?space\b|\bL\s*=\s*(SL|NL|RL)\b"
    # -- the vocabulary of hardness and bounds.
    r"|\b(NP|#P|PSPACE|EXP|QMA|W\[\d\])[- ](hard|complete|hardness|completeness)\b"
    r"|\b(lower|upper) bounds?\b|\bhardness (of|result|assumption|amplification)\b"
    r"|\b(un)?conditional lower bound\b|\bbarrier(s)?\b|\bnatural proofs\b"
    r"|\brelativi[sz](e|ation|ing)\b|\balgebri[sz]ation\b"
    r"|\boracle separation\b|\bseparat(e|es|ing|ion) .{0,30}\bclass(es)?\b"
    r"|\breduc(tion|ible|ibility)\b|\bcompleteness\b|\bdichotomy theorem\b"
    r"|\bhierarchy theorem\b|\btime[- ]space (trade[- ]?off|lower bound)\b"
    # -- the resources being measured.
    r"|\b(circuit|formula|proof|communication|query|sample|round|space|time)"
    r" complexity\b"
    r"|\bcomplexity (of|theoretic|theory)\b"
    r"|\b(circuit|formula|monotone|branching[- ]program) (size|depth|lower bound)\b",
    re.IGNORECASE,
)

# --------------------------------------------------------------------------
# Subareas (SCOPE.md § Categories)
# --------------------------------------------------------------------------

CATEGORY_PATTERNS: dict[str, str] = {
    "circuit-complexity":
        r"circuit (complexity|lower bound|size|depth|class)|boolean circuit"
        r"|\bAC\^?0\b|\bTC\^?0\b|\bNC\^?[12]\b|\bACC\^?0\b|formula (size|lower bound)"
        r"|monotone circuit|threshold circuit|constant[- ]depth|depth[- ]\d+ circuit"
        r"|branching program|switching lemma|\bDNF\b|\bCNF\b .{0,20}size",
    "algebraic-complexity":
        r"arithmetic circuit|algebraic (complexity|circuit|branching program|natural proof)"
        r"|\bVP\b|\bVNP\b|permanent (vs|versus|and) determinant|determinantal complexity"
        r"|polynomial identity testing|\bPIT\b|tensor rank|border rank|Waring rank"
        r"|matrix multiplication exponent|geometric complexity theory|\bGCT\b"
        r"|depth reduction|shallow circuit .{0,20}polynomial",
    "proof-complexity":
        r"proof complexity|resolution (refutation|width|size|lower bound)|cutting planes"
        r"|\bFrege\b|Nullstellensatz|polynomial calculus|sum[- ]of[- ]squares (proof|refutation|degree)"
        r"|bounded arithmetic|propositional proof|proof system.{0,20}(lower bound|size)"
        r"|automatability|\bLovász[- ]Schrijver\b|Sherali[- ]Adams",
    "communication-complexity":
        r"communication complexity|communication (lower bound|protocol|game)"
        r"|lifting theorem|number[- ]on[- ](fore)?head|\bNOF\b model|discrepancy (method|bound)"
        r"|information complexity|direct sum|direct product theorem|corruption bound"
        r"|log[- ]rank conjecture|streaming lower bound",
    "query-complexity":
        r"query complexity|decision tree (complexity|depth|size)|randomized query"
        r"|block sensitivity|\bsensitivity conjecture\b|certificate complexity"
        r"|approximate degree|polynomial (method|degree) .{0,20}boolean"
        r"|adversary (method|bound)|property testing|sublinear[- ]time algorithm",
    "derandomization":
        r"derandomiz|pseudorandom (generator|function|set|restriction)|\bPRG\b"
        r"|hardness (vs|versus) randomness|hitting set generator|randomness extractor"
        r"|\bextractor\b|\bdisperser\b|expander (graph|mixing)|explicit construction"
        r"|\bBPP\s*=\s*P\b|\bP\s*=\s*BPP\b|small[- ]bias|\bk[- ]wise independen",
    "hardness-of-approximation":
        r"hardness of approximation|inapproximability|approximation (hardness|resistant)"
        r"|\bPCP theorem\b|probabilistically checkable proof|unique games (conjecture)?"
        r"|\bUGC\b|label cover|gap[- ]preserving|parallel repetition"
        r"|2[- ]to[- ]2 games|small[- ]set expansion|\bCSP\b .{0,20}approxim",
    "interactive-proofs":
        r"interactive proof|zero[- ]knowledge|\bIP\s*=\s*PSPACE\b|arthur[- ]merlin"
        r"|multi[- ]prover|\bMIP\*?\b|succinct (argument|proof)|\bSNARK\b|delegation of computation"
        r"|probabilistically checkable|verifiable computation|proof of proximity"
        r"|interactive oracle proof|\bIOP\b",
    "fine-grained":
        r"fine[- ]grained (complexity|reduction|lower bound)|\bSETH\b|strong exponential time"
        r"|\bETH\b|exponential time hypothesis|\b3SUM\b|orthogonal vectors|\bOV\b conjecture"
        r"|all[- ]pairs shortest paths|\bAPSP\b|conditional lower bound"
        r"|subquadratic|subcubic|\bk[- ]clique\b .{0,20}(hard|lower)|edit distance .{0,20}(hard|lower)",
    "parameterized":
        r"parameteri[sz]ed (complexity|algorithm|reduction|intractability)"
        r"|fixed[- ]parameter tractable|\bFPT\b|kerneli[sz]ation|kernel lower bound"
        r"|\bW\[\d\]\b|W[- ]hierarchy|treewidth|\bXP\b algorithm|exact exponential algorithm",
    "meta-complexity":
        r"meta[- ]complexity|minimum circuit size problem|\bMCSP\b"
        r"|Kolmogorov complexity|\bK\^?poly\b|time[- ]bounded Kolmogorov|\bMKTP\b"
        r"|natural proofs|learning .{0,20}(from|implies) .{0,20}lower bound"
        r"|hardness magnification|\bexcluded middle\b .{0,20}complexity",
    "average-case":
        r"average[- ]case (complexity|hardness|reduction)|one[- ]way function"
        r"|distributional (NP|problem)|planted (clique|solution|distribution)"
        r"|hardness amplification|worst[- ]case to average[- ]case"
        r"|cryptographic hardness|refutation .{0,20}random|random (3-?)?SAT",
    "space-complexity":
        r"space complexity|log[- ]?space|\bL\s*(vs\.?|versus|=)\s*(NL|SL|P)\b"
        r"|catalytic (computing|space)|time[- ]space trade[- ]?off"
        r"|\bSavitch\b|tree evaluation|space[- ]bounded|small[- ]space"
        r"|\bBPL\b|\bRL\s*=\s*L\b|read[- ]once branching",
    "quantum-complexity":
        r"quantum (complexity|query|advantage|supremacy|circuit lower)"
        r"|\bBQP\b|\bQMA\b|\bQIP\b|\bQCMA\b|Hamiltonian complexity|local Hamiltonian"
        r"|quantum PCP|stabili[sz]er|\bMIP\*\b|quantum communication complexity"
        r"|\bIQP\b|random circuit sampling|boson sampling",
    "counting-complexity":
        r"counting complexity|\b#P\b|\b#CSP\b|sharp[- ]P|permanent .{0,20}(hard|comput)"
        r"|holographic algorithm|holant|partition function .{0,20}(hard|approxim)"
        r"|dichotomy (theorem|for counting)|approximate counting",
    "total-search":
        r"\bTFNP\b|\bPPAD\b|\bPLS\b|\bPPA\b|\bPPP\b|\bCLS\b"
        r"|total (search|function) problem|Nash equilibrium .{0,20}(complexity|hard)"
        r"|local search .{0,20}(complete|hard)|pigeonhole .{0,20}principle .{0,20}complexity",
    "structural":
        r"oracle separation|relativi[sz](e|ation|ing)|algebri[sz]ation"
        r"|polynomial hierarchy|hierarchy theorem|\bKarp[- ]Lipton\b|sparse set"
        r"|Berman[- ]Hartmanis|isomorphism conjecture|self[- ]reducib"
        r"|completeness .{0,20}(under|for) .{0,20}reduction|padding argument"
        r"|complexity class .{0,20}(separation|collapse|inclusion)",
    "descriptive-logic":
        r"descriptive complexity|finite model theory|\bFO\b .{0,20}(logic|definable)"
        r"|constraint satisfaction .{0,20}(dichotomy|complexity)|polymorphism"
        r"|\bFagin\b|logic .{0,20}captures .{0,20}(P|NP|PTIME)"
        r"|monadic second[- ]order|Courcelle",
}

_COMPILED = {name: re.compile(pat, re.IGNORECASE) for name, pat in CATEGORY_PATTERNS.items()}

# --------------------------------------------------------------------------
# Signals for the screening prior
# --------------------------------------------------------------------------

# Not decisive on their own. They give the screening step a prior; the abstract
# is still what the decision is made from (see prompts/mine-dataset.md).

# A new result, as opposed to a restatement of known ones.
RESULT_HINTS = re.compile(
    r"\bwe (prove|show|establish|construct|give|obtain|present|resolve|settle)\b"
    r"|\b(first|new|improved|tight|optimal|unconditional) (lower bound|upper bound|separation|construction|algorithm)\b"
    r"|\bwe (answer|resolve) .{0,30}(question|conjecture|problem)\b"
    r"|\bmain (theorem|result)\b|\bour (result|theorem|construction|technique)\b"
    r"|\bimprov(e|es|ing) (on|upon) the (previous|best[- ]known)\b",
    re.IGNORECASE,
)

# Papers that are about the field rather than results in it. Not a verdict —
# SCOPE.md decides what to do with them — but worth flagging to the screener,
# because surveys are the best snowball seeds available.
SURVEY_HINTS = re.compile(
    r"\b(survey|overview|tutorial|introduction to|lecture notes|monograph"
    r"|we survey|this survey|an exposition|expository|retrospective"
    r"|open problems? (in|list)|research directions)\b",
    re.IGNORECASE,
)


def _haystack(rec: dict) -> str:
    return clean_text(f"{rec.get('title', '')} {rec.get('abstract', '')}")


def is_complexity_paper(rec: dict) -> bool:
    return bool(COMPLEXITY_TERMS.search(_haystack(rec)))


def categorize(rec: dict) -> list[str]:
    """Every subarea whose vocabulary shows up in the title or abstract."""
    text = _haystack(rec)
    return sorted(name for name, pat in _COMPILED.items() if pat.search(text))


def in_topic(rec: dict) -> bool:
    """Complexity vocabulary *and* at least one identifiable subarea.

    The conjunction is what makes snowballing converge. Complexity terms alone
    match any paper that says "lower bound"; a subarea alone matches an applied
    paper that happens to mention treewidth.
    """
    return is_complexity_paper(rec) and bool(categorize(rec))


def screening_prior(rec: dict) -> dict:
    """Cheap signals handed to the screening step alongside the abstract."""
    text = _haystack(rec)
    return {
        "complexity": is_complexity_paper(rec),
        "categories": categorize(rec),
        "result_signal": bool(RESULT_HINTS.search(text)),
        "survey_signal": bool(SURVEY_HINTS.search(text)),
    }
