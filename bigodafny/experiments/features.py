"""Static features of a translated row, computed from the Dafny source alone.

Used for two different jobs, and the separation matters:

  * `score()` picks the 100 examples. It may use the complexity label, because
    stratifying across rare classes is a sampling decision, not a measurement.
  * `difficulty_static()` must NOT use the label. It is declared before any
    agent runs and is later compared against measured difficulty; if the label
    leaked into it, that comparison would be circular.

Nothing here calls a model. Re-running on the same tree gives the same numbers.
"""
from __future__ import annotations
import re

# A loop opens with `while`/`for` at a statement position. The bodies in this
# corpus always brace their loops, so brace depth is enough to nest them.
LOOP_RE = re.compile(r"(?:^|[\s{};])(while|for)\b")
# A conjunct is a *counter* guard when it compares one plain variable against
# an expression built only from other variables, lengths and constants:
# `i < |xs|`, `i < 2 * n`, `i < s.Length / 2`. Then the trip count is visible.
#
# Anything else is data-dependent -- a flag (`!found`), an element test
# (`s[i] == s[j]`), a value shrinking by an unknown amount (`mask != 0`) -- and
# that is where a bound stops being obvious. `827_148` is the canonical case in
# this project: no polynomial bound at all until the input values are capped.
SIMPLE_GUARD = re.compile(
    r"^\s*[A-Za-z_]\w*\s*[<>]=?\s*"
    r"(?:[A-Za-z_][\w.]*|\|[A-Za-z_]\w*\||\d+|[-+*/()\s])+$")


def split_file(text):
    """(header comment block, code). The header is where the label lives."""
    lines = text.splitlines(keepends=True)
    for i, ln in enumerate(lines):
        if ln.startswith("include "):
            return "".join(lines[:i]), "".join(lines[i:])
    return "", text


def strip_comments(code):
    code = re.sub(r"/\*.*?\*/", " ", code, flags=re.S)
    return "\n".join(ln.split("//", 1)[0] for ln in code.splitlines())


def signature(code):
    m = re.search(r"method\s+Solve\s*\(([^)]*)\)", code)
    if not m:
        return []
    out = []
    for part in m.group(1).split(","):
        part = part.strip()
        if ":" in part:
            name, ty = part.split(":", 1)
            out.append((name.strip(), ty.strip()))
    return out


def _loop_nesting(code):
    """(max nesting depth, loop count, guards). Brace-depth stack."""
    depth = 0
    stack = []          # brace depth at which each enclosing loop opened
    pending = None      # a loop keyword seen, waiting for its `{`
    maxd, count, guards = 0, 0, []
    i = 0
    while i < len(code):
        c = code[i]
        if c == "{":
            depth += 1
            if pending is not None:
                stack.append(depth)
                maxd = max(maxd, len(stack))
                guards.append(pending)
                pending = None
            i += 1
            continue
        if c == "}":
            while stack and stack[-1] > depth:
                stack.pop()
            depth -= 1
            while stack and stack[-1] > depth:
                stack.pop()
            i += 1
            continue
        m = LOOP_RE.match(code, max(0, i - 1))
        if m and m.start(1) == i:
            count += 1
            # the guard runs to the end of that line
            eol = code.find("\n", i)
            pending = code[m.end(1):eol if eol > 0 else len(code)].strip()
            i = m.end(1)
            continue
        i += 1
    return maxd, count, guards


# `x := x + [e]` / `x := x + ys` where x is a seq. Never `i := i + 1`: `1` is a
# word character, and the first version of this counted integer accumulators as
# appends, inflating the affected row count from 21 to 30.
APPEND_RE = re.compile(r"\b(\w+)\s*:=\s*\1\s*\+\s*(\[|[A-Za-z_]\w*\b(?!\s*\())")


def _loop_bodies(code):
    for m in re.finditer(r"\bwhile\b", code):
        i = code.find("{", m.end())
        if i < 0:
            continue
        d, j = 0, i
        while j < len(code):
            if code[j] == "{":
                d += 1
            elif code[j] == "}":
                d -= 1
                if d == 0:
                    break
            j += 1
        yield code[i:j]


def seq_appends_in_loops(body):
    """Sites where a loop grows a seq by concatenation -- O(len) each time."""
    n = 0
    for seg in _loop_bodies(body):
        for a in APPEND_RE.finditer(seg):
            if a.group(2) == "[" or re.search(
                    r"\b%s\s*:\s*(seq|string)" % re.escape(a.group(2)), body):
                n += 1
    return n


def drift(body, python_src):
    """Does the translation's asymptotic shape differ from its Python's?

    This is not a proof, it is a flag, and it exists because the pilot found
    the distinction the hard way. An agent that proves a bound proves it about
    the DAFNY. When the Dafny and the Python differ in shape, the proof says
    nothing about BigOBench's label, which was measured on the Python -- so a
    "refuted label" may be nothing of the kind.

    Two shapes seen in the pilot, in opposite directions:
      * `seq2 := seq2 + [x]` in a loop where the Python used `list.append`.
        Amortised O(1) in Python, O(len) per step in Dafny: a class slower.
      * `multiset(a) != multiset(b)` where the Python used `sorted(a) != sorted(b)`.
        A class faster -- linear against n log n, measured, not assumed.
    """
    py_sorts = bool(re.search(r"\bsorted\s*\(|\.sort\s*\(", python_src))
    dfy_sorts = bool(re.search(r"\bSort(?:Ints|Strings)?\s*\(", body))
    py_append = bool(re.search(r"\.append\s*\(|\+= *\[", python_src))
    appends = seq_appends_in_loops(body)
    return {
        "seq_append_in_loop": appends,
        "drift_slower": bool(appends and py_append),
        "drift_sort": py_sorts != dfy_sorts,
        "py_sorts": py_sorts,
        "dfy_sorts": dfy_sorts,
        "dfy_multiset": bool(re.search(r"\bmultiset\s*\(", body)),
    }


def extract(text):
    header, code = split_file(text)
    body = strip_comments(code)
    sig = signature(body)
    maxd, nloops, guards = _loop_nesting(body)

    # a helper that names itself is recursive
    recursive = 0
    for m in re.finditer(r"\b(?:function|method|lemma)\s+(\w+)", body):
        name = m.group(1)
        if name == "Solve":
            continue
        after = body[m.end():m.end() + 4000]
        if re.search(r"\b%s\s*\(" % re.escape(name), after):
            recursive += 1

    data_dep = sum(1 for g in guards
                   if not all(SIMPLE_GUARD.match(p)
                              for p in re.split(r"&&", g.split("{")[0].strip("() "))))

    return {
        "loop_depth": maxd,
        "loops": nloops,
        "data_dependent_loops": data_dep,
        "recursive_helpers": recursive,
        "sorts": len(re.findall(r"\bSort(?:Ints|Strings)?\s*\(", body)),
        "sets_maps": len(re.findall(r"\b(?:set<|map<|multiset\()", body)),
        "seq_args": sum(1 for _, t in sig
                        if t.startswith("seq<") or t == "string"),
        "args": len(sig),
        "body_lines": len([l for l in body.splitlines() if l.strip()]),
        "helpers": len(re.findall(r"\n\s*(?:function|method|lemma)\s+", body)),
    }


def difficulty_static(f):
    """1..5, declared before the run. Label-free by construction.

    The weights say what this project has found hard, in order: a log factor
    needs the CeilLog2 recursion-tree argument; a data-dependent guard may have
    no bound at all; nesting is where quadratic claims live.
    """
    s = 0
    s += 2 if f["sorts"] else 0
    s += 2 if f["data_dependent_loops"] else 0
    s += 1 if f["recursive_helpers"] else 0
    s += {0: 0, 1: 0, 2: 1}.get(f["loop_depth"], 2)
    s += 1 if f["sets_maps"] else 0
    s += 1 if f["body_lines"] > 60 else 0
    return max(1, min(5, 1 + s // 2))


def score(f, label_rarity):
    """Interestingness. Higher is a more informative example to spend an agent on."""
    s = 0.0
    s += 3.0 if f["loop_depth"] >= 2 else 0.0
    s += 3.0 if f["sorts"] else 0.0
    s += 3.0 if f["data_dependent_loops"] else 0.0
    s += 2.0 if f["recursive_helpers"] else 0.0
    s += 2.0 if f["sets_maps"] else 0.0
    s += 2.0 if f["seq_args"] >= 2 else 0.0
    s += f["body_lines"] / 40.0
    s += 4.0 * label_rarity
    return round(s, 3)
