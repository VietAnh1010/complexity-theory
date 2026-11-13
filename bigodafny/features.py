"""Static features of a translated row, computed from the Dafny source alone."""
from __future__ import annotations
import re

# A loop opens with `while`/`for` at a statement position. The bodies in this
# corpus always brace their loops, so brace depth is enough to nest them.
LOOP_RE = re.compile(r"(?:^|[\s{};])(while|for)\b")
# A counter guard compares one variable against variables, lengths and
# constants (`i < |xs|`, `i < 2 * n`); any other guard is data-dependent.
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


def accumulator_read_in_loop(body):
    """Is a seq accumulator read by index inside the loop that appends to it?

    That read flattens the lazy concatenation each time, making `s := s + [x]`
    quadratic. Ghost text is stripped first: an invariant's read costs nothing.
    """
    names = set(re.findall(r"(\w+)\s*:=\s*\1\s*\+\s*\[", body))
    if not names:
        return False
    blocks = _loop_blocks(body)
    for name in names:
        holding = [b for b in blocks
                   if re.search(r"\b%s\s*:=\s*%s\s*\+\s*\[" % (name, name), b)]
        if not holding:
            continue
        # The innermost enclosing loop is the one whose count multiplies the
        # flatten.
        inner = min(holding, key=len)
        live = _strip_ghost(inner)
        # `|name|` is free; `name[...]` is what forces the flatten.
        if re.search(r"\b%s\s*\[" % re.escape(name), live):
            return True
    return False


def _strip_ghost(block):
    """Drop invariant/decreases/assert/ghost lines -- erased at compile time."""
    keep = []
    for line in block.splitlines():
        s = line.strip()
        if s.startswith(("invariant", "decreases", "assert", "ghost", "//")):
            continue
        keep.append(line)
    return "\n".join(keep)


def _loop_blocks(body):
    """Each `while` and the brace-balanced block that follows it."""
    out = []
    for m in re.finditer(r"\bwhile\b", body):
        i = body.find("{", m.end())
        if i < 0:
            continue
        depth, j = 0, i
        while j < len(body):
            if body[j] == "{":
                depth += 1
            elif body[j] == "}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        out.append(body[m.start():j + 1])
    return out


def class_risk(body):
    """Does the Dafny contain a construct that can make it slower than its Python?

    `s := s[i := v]` copies the whole seq, and `s := s + {x}` rebuilds the set:
    each turns an O(n) Python loop into an O(n**2) Dafny one. A risk flag only.
    """
    seq_update = bool(re.search(r"(\w+)\s*:=\s*\1\s*\[\s*[^\]]+:=", body))
    set_build = bool(re.search(r"(\w+)\s*:=\s*\1\s*\+\s*\{", body))
    return {"seq_update_in_loop": seq_update, "set_build_in_loop": set_build,
            "class_risk": seq_update or set_build}


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

