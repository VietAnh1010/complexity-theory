"""Offline checks on the extractor. No network, no cache, ~1 second.

Every case here was a live bug found by reading extracted statements. They are
all silent failures — the counts look fine and the content is wrong — so they
belong in a test rather than in a comment.

    python3 scripts/selftest.py
"""
from __future__ import annotations
import sys

from extract import (classes_in, extract, is_problem_spec, measures_in,
                     relations_in)
from fulltext import collect_macros, detex, expand, flatten

FAILED = []


def check(name, got, want):
    ok = want(got) if callable(want) else got == want
    print(("  ok   " if ok else "  FAIL ") + name + ("" if ok else f"\n         got {got!r}"))
    if not ok: FAILED.append(name)


def doc(body, preamble=""):
    files = {"main.tex": "\\documentclass{article}\n" + preamble +
             "\n\\begin{document}\n" + body + "\n\\end{document}\n"}
    src = flatten(files, "main.tex")
    return src, files, collect_macros(files)


def cls(tex, macros=None): return sorted({c for c, _, _ in classes_in(expand(tex, macros or {}))})


print("classes")
check("ensuremath is a font wrapper", cls(r"$\ensuremath{\mathsf{NP}}$"), ["NP"])
check("author macro expands first",
      cls(r"$\cc{S_2E}$", {"cc": (1, None, r"\ensuremath{\mathsf{#1}}")}), ["S2E"])
check("the word circuit is not the class", cls(r"a circuit of size s"), [])
check("the word size is not SIZE", cls(r"of input size $n$"), [])
check("old braces-inside font", cls(r"${\rm P}={\rm NP}$"), ["NP", "P"])
check("mathcal P is a powerset", cls(r"let $\mathcal{P}(X)$ be"), [])
check("mathbb E is an expectation", cls(r"$\mathrm{\mathbb{E}}[X]$"), [])
check("E with a bracket is an expectation", cls(r"$\mathsf{E}\left[X\right]$"), [])
check("oracle superscripts merge", cls(r"$\mathsf{ZPE}^{\mathsf{NP}}$"),
      lambda g: "ZPE^NP" in g)
check("hierarchy with a variable level", cls(r"$\Sigma_k^p$"), ["SigmakP"])
check("W across a bracket", cls(r"$\mathsf{W}[1]$-hard"), ["W1"])
check("mathrm e is Euler's number", cls(r"$1-\mathrm{e}^{-100}$"), [])
check("L^2 is a function space", cls(r"for $f \in L^2(G)$"), [])
check("a one-letter class needs a numeric-free exponent",
      cls(r"$\mathrm{L}^2(R) \leq 40$"), [])
check("a one-letter class does not start mid-word",
      cls(r"$\mathsf{QIP}\textsubscript{U}\mathsf{L}$"), lambda g: "L" not in g)
check("an unexpanded macro is not a class",
      cls(r"$\mathrm{\bm{\newmathbb{E}}}[N]$"), [])

print("\nrelations")
rel = relations_in(r"$\mathsf{S_2E} \not\subset \ensuremath{i.o.}-\mathsf{SIZE}[2^n/n]$")
check("i.o. does not block the match", [(r["lhs"], r["relation"], r["rhs"]) for r in rel],
      [("S2E", "not-contained-in", "SIZE")])
check("the modifier is kept", [r["modifier"] for r in rel], ["io"])
check("the resource bound is kept", [r["rhs_arg"] for r in rel], ["[2^n/n]"])
inter = relations_in(r"$\mathsf{\Sigma_2E} \cap \mathsf{\Pi_2E} \subseteq \mathsf{PSPACE}$")
check("an intersection stays whole", [r["lhs"] for r in inter], ["Sigma2E ∩ Pi2E"])
check("the join operator is the paper's",
      [r["lhs"] for r in relations_in(r"$\mathsf{NL} \cup \mathsf{BPL} \subseteq \mathsf{P}$")],
      ["NL ∪ BPL"])
check("xspace does not block the match",
      [r["relation"] for r in relations_in(r"$\mathsf{NP}\xspace \subseteq \mathsf{PSPACE}$")],
      ["contained-in"])
check("a class the paper defines can be a side",
      [(r["lhs"], r["rhs"], r["lhs_known"]) for r in
       relations_in(r"$\mathsf{QIPL}_m[c,s] \subseteq \mathsf{P}$")],
      [("QIPL", "P", False)])
check("two unknown sides is not a claim",
      relations_in(r"$\mathsf{FOO} = \mathsf{BAR}$"), [])
check("chains give one triple per link",
      len(relations_in(r"$\mathsf{L} \subseteq \mathsf{NL} \subseteq \mathsf{P}$")), 2)

print("\nenvironments")
src, files, macros = doc(
    r"""\begin{restatable}[Named]{proposition}{propfoo}
    $\mathsf{NP} \neq \mathsf{P}$ would follow from the assumption above here.
    \end{restatable}
    \begin{myclaim}\label{c:1}Every graph in this family has an odd cycle in it.\end{myclaim}
    \begin{proof}This body must never be extracted as a statement of its own.\end{proof}
    \begin{remark}Remarks are recognized and then dropped from the kept kinds.\end{remark}""",
    r"\newtheorem{myclaim}{Claim}")
got = extract(src, files, macros)
check("restatable takes its first argument as the kind",
      [e["kind"] for e in got if e["env"] == "proposition"], ["proposition"])
check("restatable arguments are not in the statement",
      all("propfoo" not in e["statement_tex"] for e in got), True)
check("newtheorem is read from the preamble",
      [e["kind"] for e in got if e["env"] == "myclaim"], ["claim"])
check("the label is kept", [e["label"] for e in got if e["env"] == "myclaim"], ["c:1"])
check("proofs are not statements", any(e["env"] == "proof" for e in got), False)
check("remarks are not kept", any(e["kind"] == "remark" for e in got), False)
check("offsets locate the statement",
      all(src[e["char_start"]:e["char_end"]] == e["statement_tex"] for e in got), True)

print("\ntext and terms")
check("textnormal is not the word normal", detex(r"\textnormal{\sffamily NP}"), "NP")
check("cref does not leak", detex(r"see \cref{thm:main} above"), "see above")
check("escaped braces survive", detex(r"$\{0,1\}^n$"), lambda g: "{0,1}" in g)
check("texorpdfstring keeps one half", detex(r"\texorpdfstring{$\mathsf{P}$}{P}"), "P")
check("measures need a function argument", measures_in(r"$R(f) = \Omega(Q(f)^2)$"), ["Q", "R"])
check("a bare s(n) is not a measure", measures_in(r"circuits of size $s(n)$"), [])
check("prose problem specs count",
      is_problem_spec("given a circuit C, find a string outside its image", "definition"), True)
check("a plain definition is not a problem spec",
      is_problem_spec("a graph is regular if every vertex has the same degree", "definition"), False)

print(f"\n{len(FAILED)} failed")
sys.exit(1 if FAILED else 0)
