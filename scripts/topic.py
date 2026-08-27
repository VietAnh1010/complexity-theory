"""The subject. Retune here, not in lib.py.

Two traps, both learned the hard way:
  - No bare single-letter classes. `\\bP\\b` and `\\bL\\b` match ordinary prose in
    every paper ever written; they appear only inside longer phrases.
  - in_topic is a conjunction. Complexity terms alone match anything saying
    "lower bound"; a subarea alone matches applied work mentioning treewidth.
"""
from __future__ import annotations
import re
from lib import clean

TERMS = re.compile(
    r"\b(NP|coNP|PSPACE|NPSPACE|EXPTIME|EXPSPACE|NEXP|EEXP|BPP|RP|ZPP|BPL|RL"
    r"|PPAD|PLS|TFNP|PPA|PPP|CLS|FNP|FPT|XP|AC0|AC\^0|TC0|TC\^0|NC1|NC\^1|NC2|ACC0|ACC\^0"
    r"|BQP|QMA|QCMA|QIP|QSZK|StoqMA|SZK|NISZK|MA|AM|IP|MIP|PCP|PH|UP|SPP"
    r"|DTIME|NTIME|DSPACE|NSPACE|SIZE|DEPTH|VP|VNP|VBP|VF)\b"
    r"|\bP\s*(vs\.?|versus|=|≠|!=|\\neq)\s*NP\b"
    r"|\b(#|sharp[- ])P\b|\bpolynomial hierarchy\b|\bcomplexity class(es)?\b"
    r"|\b(log|logarithmic)[- ]?space\b|\bL\s*=\s*(SL|NL|RL)\b"
    r"|\b(NP|#P|PSPACE|EXP|QMA|W\[\d\])[- ](hard|complete|hardness|completeness)\b"
    r"|\b(lower|upper) bounds?\b|\bhardness (of|result|assumption|amplification)\b"
    r"|\b(un)?conditional lower bound\b|\bbarrier(s)?\b|\bnatural proofs\b"
    r"|\brelativi[sz](e|ation|ing)\b|\balgebri[sz]ation\b|\boracle separation\b"
    r"|\bseparat(e|es|ing|ion) .{0,30}\bclass(es)?\b|\breduc(tion|ible|ibility)\b"
    r"|\bcompleteness\b|\bdichotomy theorem\b|\bhierarchy theorem\b"
    r"|\btime[- ]space (trade[- ]?off|lower bound)\b"
    r"|\b(circuit|formula|proof|communication|query|sample|round|space|time) complexity\b"
    r"|\bcomplexity (of|theoretic|theory)\b"
    r"|\b(circuit|formula|monotone|branching[- ]program) (size|depth|lower bound)\b", re.I)

CATEGORIES = {
 "circuit-complexity": r"circuit (complexity|lower bound|size|depth|class)|boolean circuit|\bAC\^?0\b|\bTC\^?0\b|\bNC\^?[12]\b|\bACC\^?0\b|formula (size|lower bound)|monotone circuit|threshold circuit|constant[- ]depth|depth[- ]\d+ circuit|branching program|switching lemma|\bDNF\b|\bCNF\b .{0,20}size",
 "algebraic-complexity": r"arithmetic circuit|algebraic (complexity|circuit|branching program|natural proof)|\bVP\b|\bVNP\b|permanent (vs|versus|and) determinant|determinantal complexity|polynomial identity testing|\bPIT\b|tensor rank|border rank|Waring rank|matrix multiplication exponent|geometric complexity theory|\bGCT\b|depth reduction|shallow circuit .{0,20}polynomial",
 "proof-complexity": r"proof complexity|resolution (refutation|width|size|lower bound)|cutting planes|\bFrege\b|Nullstellensatz|polynomial calculus|sum[- ]of[- ]squares (proof|refutation|degree)|bounded arithmetic|propositional proof|proof system.{0,20}(lower bound|size)|automatability|\bLovász[- ]Schrijver\b|Sherali[- ]Adams",
 "communication-complexity": r"communication complexity|communication (lower bound|protocol|game)|lifting theorem|number[- ]on[- ](fore)?head|\bNOF\b model|discrepancy (method|bound)|information complexity|direct sum|direct product theorem|corruption bound|log[- ]rank conjecture|streaming lower bound",
 "query-complexity": r"query complexity|decision tree (complexity|depth|size)|randomized query|block sensitivity|\bsensitivity conjecture\b|certificate complexity|approximate degree|polynomial (method|degree) .{0,20}boolean|adversary (method|bound)|property testing|sublinear[- ]time algorithm",
 "derandomization": r"derandomiz|pseudorandom (generator|function|set|restriction)|\bPRG\b|hardness (vs|versus) randomness|hitting set generator|randomness extractor|\bextractor\b|\bdisperser\b|expander (graph|mixing)|explicit construction|\bBPP\s*=\s*P\b|\bP\s*=\s*BPP\b|small[- ]bias|\bk[- ]wise independen",
 "hardness-of-approximation": r"hardness of approximation|inapproximability|approximation (hardness|resistant)|\bPCP theorem\b|probabilistically checkable proof|unique games (conjecture)?|\bUGC\b|label cover|gap[- ]preserving|parallel repetition|2[- ]to[- ]2 games|small[- ]set expansion|\bCSP\b .{0,20}approxim",
 "interactive-proofs": r"interactive proof|zero[- ]knowledge|\bIP\s*=\s*PSPACE\b|arthur[- ]merlin|multi[- ]prover|\bMIP\*?\b|succinct (argument|proof)|\bSNARK\b|delegation of computation|probabilistically checkable|verifiable computation|proof of proximity|interactive oracle proof|\bIOP\b",
 "fine-grained": r"fine[- ]grained (complexity|reduction|lower bound)|\bSETH\b|strong exponential time|\bETH\b|exponential time hypothesis|\b3SUM\b|orthogonal vectors|\bOV\b conjecture|all[- ]pairs shortest paths|\bAPSP\b|conditional lower bound|subquadratic|subcubic|\bk[- ]clique\b .{0,20}(hard|lower)|edit distance .{0,20}(hard|lower)",
 "parameterized": r"parameteri[sz]ed (complexity|algorithm|reduction|intractability)|fixed[- ]parameter tractable|\bFPT\b|kerneli[sz]ation|kernel lower bound|\bW\[\d\]\b|W[- ]hierarchy|treewidth|\bXP\b algorithm|exact exponential algorithm",
 "meta-complexity": r"meta[- ]complexity|minimum circuit size problem|\bMCSP\b|Kolmogorov complexity|\bK\^?poly\b|time[- ]bounded Kolmogorov|\bMKTP\b|natural proofs|learning .{0,20}(from|implies) .{0,20}lower bound|hardness magnification|\bexcluded middle\b .{0,20}complexity",
 "average-case": r"average[- ]case (complexity|hardness|reduction)|one[- ]way function|distributional (NP|problem)|planted (clique|solution|distribution)|hardness amplification|worst[- ]case to average[- ]case|cryptographic hardness|refutation .{0,20}random|random (3-?)?SAT",
 "space-complexity": r"space complexity|log[- ]?space|\bL\s*(vs\.?|versus|=)\s*(NL|SL|P)\b|catalytic (computing|space)|time[- ]space trade[- ]?off|\bSavitch\b|tree evaluation|space[- ]bounded|small[- ]space|\bBPL\b|\bRL\s*=\s*L\b|read[- ]once branching",
 "quantum-complexity": r"quantum (complexity|query|advantage|supremacy|circuit lower)|\bBQP\b|\bQMA\b|\bQIP\b|\bQCMA\b|Hamiltonian complexity|local Hamiltonian|quantum PCP|stabili[sz]er|\bMIP\*\b|quantum communication complexity|\bIQP\b|random circuit sampling|boson sampling",
 "counting-complexity": r"counting complexity|\b#P\b|\b#CSP\b|sharp[- ]P|permanent .{0,20}(hard|comput)|holographic algorithm|holant|partition function .{0,20}(hard|approxim)|dichotomy (theorem|for counting)|approximate counting",
 "total-search": r"\bTFNP\b|\bPPAD\b|\bPLS\b|\bPPA\b|\bPPP\b|\bCLS\b|total (search|function) problem|Nash equilibrium .{0,20}(complexity|hard)|local search .{0,20}(complete|hard)|pigeonhole .{0,20}principle .{0,20}complexity",
 "structural": r"oracle separation|relativi[sz](e|ation|ing)|algebri[sz]ation|polynomial hierarchy|hierarchy theorem|\bKarp[- ]Lipton\b|sparse set|Berman[- ]Hartmanis|isomorphism conjecture|self[- ]reducib|completeness .{0,20}(under|for) .{0,20}reduction|padding argument|complexity class .{0,20}(separation|collapse|inclusion)",
 "verification-complexity": r"deductive verification|program verification|software verification|static analys|abstract interpretation|separation logic|Hoare logic|bi[- ]abduction|weakest precondition|verification condition|loop invariant|invariant (synthesis|inference|generation)|predicate abstraction|model check|symbolic execution|decision procedure|satisfiability modulo theories|\bSMT\b|constrained Horn clause|Craig interpolat|refinement type|dependent type|type (inference|checking) .{0,20}(complexity|decidab)|pointer analysis|alias analysis|shape analysis|termination analysis|proof assistant|cost analysis|resource analysis|resource bound|runtime bound|loop bound|worst[- ]case execution time|\bWCET\b|amortized (analysis|complexity|resource)|time credit|complexity (bug|vulnerabilit)|performance regression|algorithmic complexity attack|\bFrama-?C\b|\bDafny\b|\bWhy3\b|\bViper\b|\bVeriFast\b|\bBoogie\b|\bCBMC\b|\bSeaHorn\b|\bACSL\b|\bSPARK Ada\b|\bKeY\b .{0,20}(Java|verif)",
 "descriptive-logic": r"descriptive complexity|finite model theory|\bFO\b .{0,20}(logic|definable)|constraint satisfaction .{0,20}(dichotomy|complexity)|polymorphism|\bFagin\b|logic .{0,20}captures .{0,20}(P|NP|PTIME)|monadic second[- ]order|Courcelle",
}
_C = {n: re.compile(p, re.I) for n, p in CATEGORIES.items()}

# Second admission path, for `verification-complexity` only. The resource there
# is the cost of *checking* a program: decision-procedure complexity, or the
# analysis cost a real codebase imposes. A tool paper reporting neither is a
# demo, and stays out.
VERIF_TERMS = re.compile(
    r"\b(un)?decidab(le|ility)\b|\bsemi[- ]decidab|\bdecision procedure\b"
    r"|\bstate[- ](space )?explosion\b|\bexponential blow[- ]?up\b"
    r"|\bcomplexity of (verification|model checking|program analysis|analysis|inference|type checking)\b"
    r"|\bscal(e|es|ing|able|ability|ability)\b .{0,40}\b(code|codebase|program|software|line|system)"
    r"|\bscal(e|es|ing) to\b|\blarge[- ](scale|sized) (code|codebase|program|software|system)"
    r"|\bmillions? of lines\b|\blines of (code|source)\b|\bwhole[- ]program\b"
    r"|\breal[- ]world (code|software|program|system)|\bindustrial (scale|code|deployment)\b"
    r"|\b(modular|compositional|incremental|summary[- ]based|interprocedural) "
    r"(analys(is|es)|verification|reasoning|proof|checking)\b"
    r"|\bproof (burden|effort|automation)\b|\bannotation burden\b|\bverification effort\b"
    r"|\bworst[- ]case (complexity|running time|cost|bound)\b", re.I)


# Priors for screening, not verdicts.
RESULT = re.compile(r"\bwe (prove|show|establish|construct|give|obtain|present|resolve|settle)\b"
                    r"|\b(first|new|improved|tight|optimal|unconditional) (lower bound|upper bound|separation|construction|algorithm)\b"
                    r"|\bwe (answer|resolve) .{0,30}(question|conjecture|problem)\b"
                    r"|\bmain (theorem|result)\b|\bour (result|theorem|construction|technique)\b"
                    r"|\bimprov(e|es|ing) (on|upon) the (previous|best[- ]known)\b", re.I)
SURVEY = re.compile(r"\b(survey|overview|tutorial|introduction to|lecture notes|monograph"
                    r"|we survey|this survey|an exposition|expository|retrospective"
                    r"|open problems? (in|list)|research directions)\b", re.I)


def _h(r): return clean(f"{r.get('title','')} {r.get('abstract','')}")
def is_complexity(r): return bool(TERMS.search(_h(r)))
def categorize(r): return sorted(n for n, p in _C.items() if p.search(_h(r)))
def is_verification(r): return bool(VERIF_TERMS.search(_h(r)))


def in_topic(r):
    """A conjunction, as before, plus one alternative for the verification tier:
    a cost-of-checking claim stands in for the complexity vocabulary there."""
    cats = categorize(r)
    if not cats: return False
    return is_complexity(r) or ("verification-complexity" in cats and is_verification(r))


def prior(r):
    t = _h(r)
    return {"complexity": bool(TERMS.search(t)), "categories": categorize(r),
            "cost_of_checking": bool(VERIF_TERMS.search(t)),
            "result_signal": bool(RESULT.search(t)), "survey_signal": bool(SURVEY.search(t))}
