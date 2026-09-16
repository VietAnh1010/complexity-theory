"""Call graph of a row's Dafny, and the longest acyclic chain from `Solve`.

How deep a row's call structure runs is a property of the translation, not of
the problem, and it is the kind of thing that only becomes visible in aggregate:
a corpus where every row is one flat `Solve` is a different artifact from one
where half the rows build three levels of helpers.

Scope. Only `solutions/` -- the clean rows. `solutions-tofix/` holds rows whose
labels are disputed and whose bodies may be rewritten, so measuring their shape
now would measure something about to change.

What counts as an edge. A call from one declaration in the file to another
declaration **in the same file**, plus calls into `prelude.dfy`, which are
resolved against the prelude's own graph so a row that calls `SortInts` inherits
the depth underneath it. Everything else -- Dafny builtins, `|s|`, sequence
operations -- is a leaf and contributes no depth.

Depth is measured as the longest simple path from `Solve`, so a cycle cannot
inflate it. Recursion is real and common here (it is how most of these rows
express iteration over a sequence), so cycles are reported separately rather
than silently collapsed: `longest_chain` is the acyclic answer the task asks
for, and `recursive` says whether that number is the whole story.

Two numbers, deliberately separate:

  longest_chain   the longest simple path, in edges, from Solve
  reachable       how many declarations Solve can reach at all

A row can be wide and shallow (many helpers, all called directly from Solve) or
narrow and deep. One number would hide which.
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import DATA, ROOT, SOLUTIONS, log, write_jsonl      # noqa: E402

# A declaration header. Dafny lets `function`, `method`, `predicate` and `lemma`
# carry modifiers (`ghost`, `opaque`, `least`, `twostate`) and attributes
# (`{:opaque}`), so the name is taken after all of them.
DECL = re.compile(
    r"^\s*(?:ghost\s+|opaque\s+|least\s+|greatest\s+|twostate\s+|static\s+)*"
    r"(function|method|predicate|lemma|constructor)\b"
    r"(?:\s+method)?"                      # `function method`, Dafny 3 style
    r"(?:\s*\{[^}]*\})*"                   # {:opaque}, {:induction false}, ...
    r"\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.M)

# Anything that looks like `Name(`. Over-matches -- it will catch `if (`, a type
# name, a local variable used as a function value -- so every hit is kept only
# when it resolves to a declaration we know about. That makes false positives
# harmless and keeps the matcher simple.
CALL = re.compile(r"\b([A-Za-z_][A-Za-z0-9_']*)\s*\(")

# Dafny keywords that are followed by `(` and are not calls.
KEYWORDS = {
    "if", "while", "for", "assert", "assume", "expect", "print", "return",
    "requires", "ensures", "invariant", "decreases", "modifies", "reads",
    "forall", "exists", "match", "case", "old", "fresh", "unchanged", "new",
    "seq", "set", "map", "multiset", "array", "imap", "iset", "var", "yield",
    "calc", "by", "then", "else", "in", "this", "assert_by", "reveal", "let",
}


def strip_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", "", text)


def declarations(text):
    """Map each declaration name to the source span of its body.

    Spans run from one declaration header to the next. That is coarser than a
    brace-matched body -- a trailing `}` and any blank lines belong to the
    preceding span -- but call extraction only cares which names appear between
    two headers, and brace matching would have to understand string literals,
    character literals and set-display braces to do better.
    """
    hits = [(m.start(), m.group(2), m.start(2), m.group(0), m.group(1))
            for m in DECL.finditer(text)]
    spans, kinds = {}, {}
    for i, (pos, name, name_at, header, kw) in enumerate(hits):
        end = hits[i + 1][0] if i + 1 < len(hits) else len(text)
        # A lemma is always ghost; `function`/`predicate` are ghost only when
        # declared so. Ghost declarations are erased by `dafny translate`, so a
        # chain through them is proof structure, not anything that runs.
        kinds[name] = ("ghost" if kw == "lemma" or "ghost" in header
                       else "exec")
        # A name declared twice in one file (overloads are illegal in Dafny, but
        # a row can redeclare a prelude helper locally) keeps its first span and
        # extends to cover the second, so no calls are lost.
        if name in spans:
            spans[name] = (spans[name][0], end, spans[name][2] | {name_at})
        else:
            spans[name] = (pos, end, {name_at})
    return spans, kinds


def graph_of(text, known=None):
    """Adjacency from declaration name to the declarations it calls."""
    text = strip_comments(text)
    spans, kinds = declarations(text)
    universe = set(spans) | set(known or ())
    g = {}
    for name, (start, end, header_offsets) in spans.items():
        body = text[start:end]
        callees = set()
        for m in CALL.finditer(body):
            callee = m.group(1)
            if callee in KEYWORDS:
                continue
            # The declaration's own header contains its name followed by `(`.
            # Skip exactly that occurrence, by absolute position -- an earlier
            # version skipped any self-call in the first 200 characters, which
            # silently erased the recursion in every short recursive function
            # (`Gcd` among them) and reported those rows as acyclic.
            if start + m.start() in header_offsets:
                continue
            if callee in universe:
                callees.add(callee)
        g[name] = sorted(callees)
    return g, kinds


def longest_simple_path(g, start):
    """Longest path from `start` that repeats no node, in edges.

    Exponential in the worst case; these graphs have at most a few dozen nodes
    and are near-trees, so it runs instantly. `limit` guards the pathological
    case rather than trusting that.
    """
    best = [0]
    best_path = [[start]]
    steps = [0]
    LIMIT = 200_000

    def walk(node, seen, path):
        steps[0] += 1
        if steps[0] > LIMIT:
            return
        if len(path) - 1 > best[0]:
            best[0] = len(path) - 1
            best_path[0] = list(path)
        for nxt in g.get(node, ()):
            if nxt in seen:
                continue
            seen.add(nxt); path.append(nxt)
            walk(nxt, seen, path)
            path.pop(); seen.discard(nxt)

    walk(start, {start}, [start])
    return best[0], best_path[0], steps[0] > LIMIT


def reachable_from(g, start):
    seen, stack = set(), [start]
    while stack:
        n = stack.pop()
        for m in g.get(n, ()):
            if m not in seen:
                seen.add(m); stack.append(m)
    return seen


def has_cycle(g, nodes):
    """True if any node reachable from Solve sits on a cycle (incl. self-loop)."""
    WHITE, GREY, BLACK = 0, 1, 2
    colour = {n: WHITE for n in nodes}
    found = [False]

    def dfs(n):
        colour[n] = GREY
        for m in g.get(n, ()):
            if m not in colour:
                continue
            if colour[m] == GREY:
                found[0] = True
            elif colour[m] == WHITE:
                dfs(m)
        colour[n] = BLACK

    for n in list(colour):
        if colour[n] == WHITE:
            dfs(n)
    return found[0]


def prelude_graph():
    p = ROOT / "prelude.dfy"
    if not p.exists():
        log("warning: prelude.dfy not found; prelude calls will be leaves")
        return {}, {}
    return graph_of(p.read_text(encoding="utf-8"))


def analyse(path, pre_pair):
    pre, pre_kinds = pre_pair
    text = path.read_text(encoding="utf-8")
    own, own_kinds = graph_of(text, known=set(pre))
    # Row declarations win over prelude ones of the same name: a row that
    # defines its own ParseIntFrom is calling that, not the prelude's.
    g = dict(pre)
    g.update(own)
    kinds = dict(pre_kinds)
    kinds.update(own_kinds)

    # The executable graph: ghost declarations dropped entirely, so a chain
    # cannot pass through a lemma. Without this the deepest row in the corpus
    # is 1386_19 at 5, whose whole chain is the prelude's sortedness proof --
    # a number about verification, not about what the program does.
    gx = {n: [m for m in cs if kinds.get(m, "exec") == "exec"]
          for n, cs in g.items() if kinds.get(n, "exec") == "exec"}

    entry = "Solve"
    if entry not in g:
        return {"path": str(path.relative_to(ROOT)), "sid": path.stem,
                "problem_id": path.parent.name, "status": "no-Solve"}

    reach = reachable_from(g, entry)
    cyclic = has_cycle(g, reach | {entry})
    depth, chain, truncated = longest_simple_path(g, entry)
    xdepth, xchain, xtrunc = longest_simple_path(gx, entry)
    xreach = reachable_from(gx, entry)
    return {
        "sid": path.stem,
        "problem_id": path.parent.name,
        "path": str(path.relative_to(ROOT)),
        "status": "ok",
        # The headline number: longest executable chain, ghost code excluded.
        "longest_chain": xdepth,             # edges from Solve
        "longest_chain_path": xchain,
        "reachable": len(xreach),
        # The same over the full graph, lemmas included, for comparison.
        "longest_chain_with_ghost": depth,
        "longest_chain_with_ghost_path": chain,
        "reachable_with_ghost": len(reach),
        "own_decls": len(own),
        "prelude_calls": sorted(n for n in reach if n in pre and n not in own),
        "recursive": cyclic,
        "search_truncated": truncated or xtrunc,
    }


def run(limit=None, only=None, out=None):
    pre = prelude_graph()
    log(f"prelude: {len(pre[0])} declarations "
        f"({sum(1 for k in pre[1].values() if k == 'ghost')} ghost)")
    rows = []
    for p in sorted(SOLUTIONS.rglob("*.dfy"),
                    key=lambda q: (int(q.parent.name), q.stem)):
        if only and p.stem not in only:
            continue
        rows.append(analyse(p, pre))
        if limit and len(rows) >= limit:
            break

    out = out or (DATA / "call_depth.jsonl")
    write_jsonl(out, rows)

    ok = [r for r in rows if r["status"] == "ok"]
    bad = [r for r in rows if r["status"] != "ok"]
    if ok:
        depths = [r["longest_chain"] for r in ok]
        hist = {}
        for d in depths:
            hist[d] = hist.get(d, 0) + 1
        log(f"{len(ok)} rows analysed -> {out.relative_to(ROOT)}")
        log(f"  longest chain: min {min(depths)}, max {max(depths)}, "
            f"mean {sum(depths)/len(depths):.2f}")
        log("  depth histogram: " +
            ", ".join(f"{d}:{hist[d]}" for d in sorted(hist)))
        log(f"  recursive rows: {sum(1 for r in ok if r['recursive'])}")
        gdepths = [r["longest_chain_with_ghost"] for r in ok]
        log(f"  with ghost code included: max {max(gdepths)}, "
            f"mean {sum(gdepths)/len(gdepths):.2f}")
        deepest = max(ok, key=lambda r: r["longest_chain"])
        log(f"  deepest executable: {deepest['sid']} at "
            f"{deepest['longest_chain']} -> "
            + " -> ".join(deepest["longest_chain_path"]))
    if bad:
        log(f"  {len(bad)} row(s) with no Solve: "
            + ", ".join(r["sid"] for r in bad[:8]))
    return rows


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int)
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--out", type=Path)
    ap.add_argument("--show", help="print one row's graph and exit")
    a = ap.parse_args()
    if a.show:
        pre = prelude_graph()
        hits = [p for p in SOLUTIONS.rglob(f"{a.show}.dfy")]
        if not hits:
            log(f"no such row in solutions/: {a.show}"); sys.exit(1)
        r = analyse(hits[0], pre)
        print(json.dumps(r, indent=1))
    else:
        run(a.limit, a.only, a.out)
