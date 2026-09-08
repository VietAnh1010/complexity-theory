"""Check every `requires` added to a translation against every stored input.

Adding a precondition is the cheap way to make `dafny verify` pass: narrow the
contract until the obligation is trivial. That is only honest if the precondition
is something the problem actually guarantees. If it fails on inputs the harness
really feeds, the proof covers a domain the data does not visit.

This translates the common Dafny precondition shapes into Python and evaluates
them against the parsed test inputs. Shapes it cannot translate are reported as
`unchecked` -- they need reading, not guessing.
"""
from __future__ import annotations
import json, re, sys
from pathlib import Path

from common import DATA, INEXACT, SOLUTIONS, UNVERIFIED, log, read_jsonl, write_jsonl
from signature import input_fields

ROOTS = [SOLUTIONS, UNVERIFIED, INEXACT]


def find(sid, pid):
    for r in ROOTS:
        p = r / pid / f"{sid}.dfy"
        if p.exists():
            return p
    return None


def requires_of(text):
    head = text.split("method Solve(", 1)[1].split("{", 1)[0] if "method Solve(" in text else ""
    out, cur = [], None
    for line in head.splitlines():
        s = line.split("//", 1)[0].strip()   # a comment is never part of a clause
        if not s:
            continue
        if s.startswith("requires "):
            if cur:
                out.append(cur)
            cur = s[len("requires "):]
        elif cur is not None and s and not s.startswith(("ensures", "decreases", "modifies")):
            cur += " " + s
        elif cur:
            out.append(cur); cur = None
    if cur:
        out.append(cur)
    return [re.sub(r"\s+", " ", c).strip() for c in out]


FIELDS: set = set()


def unrename(w):
    """Undo signature.py's keyword dodge: it appends `_` until the name is legal."""
    if w in FIELDS:
        return w
    cand = w
    while cand.endswith("_"):
        cand = cand[:-1]
        if cand in FIELDS:
            return cand
    return w


def _mask_literals(s):
    """Hide quoted char/string literals so the field rewrite cannot reach inside.

    Without this, `'A' <= c <= 'Z'` became `'I.A' <= I.c <= 'I.Z'` -- still valid
    Python, silently False, and reported as a VIOLATED precondition.
    """
    lits = []
    def take(mo):
        lits.append(mo.group(0))
        return f"\x00{len(lits)-1}\x00"
    return re.sub(r"'(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\"", take, s), lits


def _unmask_literals(s, lits):
    for i, lit in enumerate(lits):
        s = s.replace(f"\x00{i}\x00", lit)
    return s


# Python keywords can precede "(" without being a call: `for _t in (x).split()`.
ALLOWED_CALLS = {"len", "int", "sum", "abs", "max", "min", "all", "any",
                 "range", "split",
                 "in", "for", "if", "else", "not", "and", "or"}


def _unknown_call(s):
    """True if `s` calls something we cannot evaluate in Python."""
    return any(mo.group(1) not in ALLOWED_CALLS
               for mo in re.finditer(r"(?<![.\w|])([A-Za-z_]\w*)\s*\(", s))


def _len_bars(s):
    """`|X|` -> `len(X)` for an arbitrary balanced X, not just a bare name."""
    out, i = "", 0
    while i < len(s):
        if s[i] == "|":
            depth, j = 0, i + 1
            while j < len(s):
                c = s[j]
                if c in "([":
                    depth += 1
                elif c in ")]":
                    depth -= 1
                elif c == "|" and depth == 0:
                    break
                j += 1
            if j < len(s):
                out += "len(" + _len_bars(s[i + 1:j]) + ")"
                i = j + 1
                continue
        out += s[i]
        i += 1
    return out


def _balanced_arg(s, i):
    """Text of the parenthesised argument starting at s[i] == '(' , and the index after it."""
    depth, j = 0, i
    while j < len(s):
        if s[j] == "(":
            depth += 1
        elif s[j] == ")":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    return None, None


def _prelude_calls(s):
    """Rewrite the prelude functions that show up inside preconditions.

    Without these the clause hits the unknown-call guard and is reported
    `unchecked` -- which reads as "needs a human", not "checked".
    """
    reps = [("ParseInts(SplitWs(", "PARSEINTSPLIT"),
            ("ParseInts(", "PARSEINTS"), ("SplitWs(", "SPLITWS"),
            ("ParseInt(", "PARSEINT"), ("SumSeq(", "SUMSEQ")]
    changed = True
    while changed:
        changed = False
        for name, _ in reps:
            i = s.find(name)
            if i < 0:
                continue
            open_at = i + len(name) - 1
            if name == "ParseInts(SplitWs(":
                open_at = i + len("ParseInts(SplitWs") - len("SplitWs")
                arg, end = _balanced_arg(s, i + len("ParseInts") )
                if arg is None:
                    return s
                inner, _ = _balanced_arg(arg, arg.find("("))
                if inner is None:
                    return s
                s = s[:i] + f"[int(_t) for _t in ({inner}).split()]" + s[end:]
            else:
                arg, end = _balanced_arg(s, open_at)
                if arg is None:
                    return s
                body = {"ParseInts(": f"[int(_t) for _t in ({arg})]",
                        "SplitWs(": f"({arg}).split()",
                        "ParseInt(": f"int({arg})",
                        "SumSeq(": f"sum({arg})"}[name]
                s = s[:i] + body + s[end:]
            changed = True
            break
    return s


def to_python(clause, bound=()):
    """Translate one Dafny precondition into a Python expression over `I`."""
    s = clause
    # A call to a Dafny function we cannot evaluate makes the clause
    # untranslatable. Checked after the prelude rewrite, against a whitelist of
    # the calls that rewrite itself emits -- see _unknown_call.
    if _unknown_call(_prelude_calls(_mask_literals(s)[0])):
        return None
    m = re.match(r"forall (\w+) :: 0 <= \1 < (\|\w+\||\w+) ==> (.+)$", s)
    if m:
        var, hi, body = m.groups()
        inner = to_python(body, tuple(bound) + (var,))
        if inner is None:
            return None
        hi_py = (f"len(I.{unrename(hi[1:-1])})" if hi.startswith("|")
                 else f"I.{unrename(hi)}")
        return f"all(({inner}) for {var} in range({hi_py}))"
    # exists over an index range
    m = re.match(r"exists (\w+) :: 0 <= \1 < (\|\w+\||\w+) && (.+)$", s)
    if m:
        var, hi, body = m.groups()
        inner = to_python(body, tuple(bound) + (var,))
        if inner is None:
            return None
        hi_py = (f"len(I.{unrename(hi[1:-1])})" if hi.startswith("|")
                 else f"I.{unrename(hi)}")
        return f"any(({inner}) for {var} in range({hi_py}))"
    # quantifier over an arbitrary numeric range
    m = re.match(r"(forall|exists) (\w+) :: (.+?) <= \2 (<=?) (.+?) (?:==>|&&) (.+)$", s)
    if m:
        kind, var, lo, op, hi, body = m.groups()
        parts = [to_python(x, tuple(bound) + (var,)) for x in (lo, hi, body)]
        if any(x is None for x in parts):
            return None
        lo_py, hi_py, inner = parts
        stop = f"({hi_py}) + 1" if op == "<=" else f"({hi_py})"
        fn = "all" if kind == "forall" else "any"
        return f"{fn}(({inner}) for {var} in range({lo_py}, {stop}))"
    # quantifier over the ELEMENTS of a sequence, not its indices
    m = re.match(r"(forall|exists) (\w+) :: \2 in (\w+) (?:==>|&&) (.+)$", s)
    if m:
        kind, var, xs, body = m.groups()
        inner = to_python(body, tuple(bound) + (var,))
        if inner is None:
            return None
        fn = "all" if kind == "forall" else "any"
        return f"{fn}(({inner}) for {var} in I.{unrename(xs)})"
    # implication at the top level
    m = re.match(r"(.+?) ==> (.+)$", s)
    if m and "::" not in m.group(1):
        a, b = (to_python(x, bound) for x in m.groups())
        if a is None or b is None:
            return None
        return f"((not ({a})) or ({b}))"
    s = s.replace("&&", " and ").replace("||", " or ")
    s = _prelude_calls(s)
    s = _len_bars(s)
    s = re.sub(r"(\w+)\[(\w+)\]\.(\d)", r"\1[\2][\3]", s)
    if _unknown_call(_mask_literals(s)[0]):
        return None
    # bare identifiers that are not python keywords/numbers -> Input fields
    def field(mo):
        w = mo.group(0)
        if w in ("and", "or", "not", "in", "if", "else", "for", "len", "all",
                 "any", "int", "sum", "abs", "max", "min", "range", "I",
                 "true", "false", "_t") or w in bound:
            return w
        return f"I.{unrename(w)}"
    s, lits = _mask_literals(s)
    s = re.sub(r"(?<![.\w])[a-zA-Z_]\w*(?![\w(])", field, s)
    return _unmask_literals(s, lits)


def run(sids):
    tasks = {t["solution_id"]: t for t in read_jsonl(DATA / "tasks.jsonl")}
    rows = []
    for sid in sids:
        pid = sid.split("_")[0]
        p = find(sid, pid)
        if p is None or sid not in tasks:
            continue
        clauses = requires_of(p.read_text(encoding="utf-8"))
        if not clauses:
            continue
        t = tasks[sid]
        ns = {}
        exec(compile(t["dataclass_code"], "<dc>", "exec"), ns)
        global FIELDS
        try:
            FIELDS = {n for n, _ in input_fields(t["dataclass_code"])}
        except Exception:
            FIELDS = set()
        for c in clauses:
            expr = to_python(c)
            rec = {"solution_id": sid, "clause": c, "expr": expr,
                   "holds": 0, "violated": 0, "error": 0}
            if expr is None:
                rec["status"] = "unchecked"
                rows.append(rec); continue
            for k in ("public_tests", "private_tests", "generated_tests"):
                for tst in t["tests"].get(k, []):
                    try:
                        I = ns["Input"].from_str(tst["input"])
                        val = eval(expr, {"len": len, "all": all,
                                          "range": range, "I": I})
                        rec["holds" if val else "violated"] += 1
                    except Exception:
                        rec["error"] += 1
            rec["status"] = ("violated" if rec["violated"] else
                             "ok" if rec["holds"] else "no-data")
            rows.append(rec)
    write_jsonl(DATA / "precondition_check.jsonl", rows)
    bad = [r for r in rows if r["status"] == "violated"]
    unk = [r for r in rows if r["status"] == "unchecked"]
    nod = [r for r in rows if r["status"] == "no-data"]
    log(f"preconditions: {len(rows)} clauses over {len({r['solution_id'] for r in rows})} rows")
    log(f"  ok        {sum(1 for r in rows if r['status']=='ok')}")
    log(f"  VIOLATED  {len(bad)}")
    log(f"  unchecked {len(unk)}  (needs reading, not guessing)")
    log(f"  no-data   {len(nod)}  (translated but never evaluated -- NOT a pass)")
    for r in bad:
        log(f"    VIOLATED {r['solution_id']}: {r['clause']}  "
            f"(holds {r['holds']}, violated {r['violated']})")
    for r in unk:
        log(f"    unchecked {r['solution_id']}: {r['clause']}")
    for r in nod:
        log(f"    no-data {r['solution_id']}: {r['clause']}  "
            f"(errors {r['error']})")
    return rows


if __name__ == "__main__":
    ids = sys.argv[1:]
    if not ids:
        print("usage: precheck.py SID..."); sys.exit(2)
    run(ids)
