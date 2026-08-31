"""dataclass_code -> Dafny method signature.

The Python solutions are stdin scripts with no signature; the `Input` dataclass
that BigOBench generated for fuzzing is the only typed argument list in the
data. This module recovers it with `ast` -- never a regex, because an
annotation is a Python expression and regexes get nested generics wrong.

Deterministic: same input, same output, no model.
"""
from __future__ import annotations
import ast
from collections import Counter

from common import DATA, event, log, read_jsonl, write_jsonl

SCALARS = {"int": "int", "str": "string", "float": "real", "bool": "bool"}

# Dafny 4.x keywords. A field named `map` or `set` is legal Python and is not a
# legal Dafny parameter name.
RESERVED = {
    "abstract", "allocated", "as", "assert", "assume", "bool", "break", "by",
    "calc", "case", "char", "class", "codatatype", "colemma", "const",
    "constructor", "continue", "datatype", "decreases", "else", "ensures",
    "exists", "expect", "export", "extends", "false", "for", "forall", "fresh",
    "function", "ghost", "if", "imap", "import", "in", "include", "int",
    "invariant", "is", "iset", "iterator", "label", "lemma", "map", "match",
    "method", "modifies", "modify", "module", "multiset", "nameonly", "nat",
    "new", "newtype", "null", "object", "old", "opaque", "opened", "ord",
    "predicate", "print", "provides", "reads", "real", "refines", "requires",
    "return", "returns", "reveal", "seq", "set", "static", "string", "then",
    "this", "trait", "true", "twostate", "type", "unchanged", "var", "while",
    "witness", "yield", "yields",
}
RETURN_NAME = "output"


class Unmappable(Exception):
    pass


def _generic(node):
    """Return (name, args) for List[int] / Tuple[int, int], else (None, None)."""
    if not isinstance(node, ast.Subscript):
        return None, None
    v = node.value
    name = v.id if isinstance(v, ast.Name) else \
        v.attr if isinstance(v, ast.Attribute) else None
    s = node.slice
    args = list(s.elts) if isinstance(s, ast.Tuple) else [s]
    return name, args


def dafny_type(node):
    """Map one annotation AST node to a Dafny type, or raise Unmappable."""
    if isinstance(node, ast.Name) and node.id in SCALARS:
        return SCALARS[node.id]
    if isinstance(node, ast.Attribute) and node.attr in SCALARS:
        return SCALARS[node.attr]

    name, args = _generic(node)
    if name in ("List", "list", "Sequence") and args and len(args) == 1:
        return f"seq<{dafny_type(args[0])}>"
    if name in ("Tuple", "tuple") and args:
        # Dafny writes a 1-tuple as the bare type, not `(T)`.
        inner = ", ".join(dafny_type(a) for a in args)
        return inner if len(args) == 1 else f"({inner})"

    raise Unmappable(ast.unparse(node))


def safe_name(n, taken):
    """Dafny-legal parameter name that collides with nothing."""
    out = n
    while out in RESERVED or out == RETURN_NAME or out in taken:
        out += "_"
    return out


def input_fields(dataclass_code):
    """The annotated fields of `class Input`, in declaration order."""
    tree = ast.parse(dataclass_code)
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef) and node.name == "Input":
            return [(s.target.id, s.annotation) for s in node.body
                    if isinstance(s, ast.AnnAssign) and isinstance(s.target, ast.Name)]
    raise Unmappable("no `class Input` in dataclass_code")


def synthesize(dataclass_code):
    """-> {status, params, dafny, ...}. Never raises; records the reason."""
    try:
        fields = input_fields(dataclass_code)
    except SyntaxError as e:
        return {"status": "unmappable", "reason": f"dataclass_code parse error: {e}"}
    except Unmappable as e:
        return {"status": "unmappable", "reason": str(e)}

    if not fields:
        return {"status": "unmappable", "reason": "`class Input` has no annotated fields"}

    params, taken = [], set()
    for py_name, ann in fields:
        try:
            dt = dafny_type(ann)
        except Unmappable as e:
            return {"status": "unmappable",
                    "reason": f"unsupported annotation for `{py_name}`: {e}"}
        dn = safe_name(py_name, taken)
        taken.add(dn)
        params.append({"py_name": py_name, "dafny_name": dn,
                       "py_type": ast.unparse(ann), "dafny_type": dt})

    args = ", ".join(f'{p["dafny_name"]}: {p["dafny_type"]}' for p in params)
    return {"status": "ok", "params": params, "arity": len(params),
            "dafny": f"method Solve({args}) returns ({RETURN_NAME}: string)"}


def build():
    """One signature per problem -- dataclass_code is constant within a problem."""
    tasks = list(read_jsonl(DATA / "tasks.jsonl"))
    by_problem = {}
    for t in tasks:
        prev = by_problem.get(t["problem_id"])
        if prev is not None and prev["dataclass_code"] != t["dataclass_code"]:
            event("dataclass_differs_within_problem", problem_id=t["problem_id"])
        by_problem.setdefault(t["problem_id"], t)

    out = []
    for pid, t in sorted(by_problem.items(), key=lambda kv: int(kv[0])):
        sig = synthesize(t["dataclass_code"])
        out.append({"problem_id": pid, "problem_name": t["problem_name"], **sig})

    write_jsonl(DATA / "signatures.jsonl", out)
    st = Counter(s["status"] for s in out)
    log(f"signatures: {st['ok']}/{len(out)} ok, {st['unmappable']} unmappable")
    for s in out:
        if s["status"] == "unmappable":
            log(f"  unmappable {s['problem_id']} {s['problem_name']}: {s['reason']}")
    event("signatures", ok=st["ok"], unmappable=st["unmappable"], total=len(out))
    return out


if __name__ == "__main__":
    build()
