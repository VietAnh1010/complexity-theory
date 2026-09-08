"""Classify a proved `ensures steps <= EXPR` into one of the 11 label classes.

Mechanical, not a judgement call. The method is a growth probe: substitute
numbers for the size atoms in the expression, do the same for each candidate
class, and keep the candidates whose ratio to the expression stays bounded as
the atoms grow. `EXPR` is a polynomial in sizes with at most a `CeilLog2`
factor, so the ratio converges exactly when the class is right.

Why a probe rather than a parser: the constants are arbitrary by design (the
guide tells agents not to tune them), the expressions nest parentheses freely
(`(n + 2) * (n + 2) + 8 * (n + 2) + 20`), and new shapes appear whenever a proof
charges a term the label does not name (`2 * n * n + ... + 2 * SumLen(numbers)`).
A probe handles all of those without a grammar.

Two things it deliberately does NOT do:

  * decide which argument of `Solve` is the label's `n`. That mapping is not
    declared anywhere in BigOBench, and assuming one is how two labels in this
    corpus came to be wrong. The probe reports the *shape* and tries every
    assignment of atoms to n and m; `size_mapping` in the agent's result says
    what the agent believed.
  * silently round. An expression it cannot place returns `unclassified`, which
    is reported and adjudicated, never counted as a match.
"""
from __future__ import annotations
import math, re

CLASSES = ["O(1)", "O(logn)", "O(n)", "O(n+m)", "O(nlogn)", "O(n*m)",
           "O(n**2)", "O(n+mlogm)", "O(nlogn+mlogm)", "O(n+m)log(n+m)",
           "O(n**2+m**2)"]

# Each candidate as a growth function of (n, m). One-atom classes ignore m.
CAND = {
    "O(1)":            (1, lambda n, m: 1.0),
    "O(logn)":         (1, lambda n, m: _lg(n)),
    "O(n)":            (1, lambda n, m: n),
    "O(nlogn)":        (1, lambda n, m: n * _lg(n)),
    "O(n**2)":         (1, lambda n, m: n * n),
    "O(n+m)":          (2, lambda n, m: n + m),
    "O(n*m)":          (2, lambda n, m: n * m),
    "O(n+mlogm)":      (2, lambda n, m: n + m * _lg(m)),
    "O(nlogn+mlogm)":  (2, lambda n, m: n * _lg(n) + m * _lg(m)),
    "O(n+m)log(n+m)":  (2, lambda n, m: (n + m) * _lg(n + m)),
    "O(n**2+m**2)":    (2, lambda n, m: n * n + m * m),
}
# Tighter first: a linear expression matches O(n**2) as an upper bound too, and
# the tightest true class is the informative one.
ORDER = ["O(1)", "O(logn)", "O(n)", "O(n+m)", "O(nlogn)", "O(nlogn+mlogm)",
         "O(n+mlogm)", "O(n+m)log(n+m)", "O(n*m)", "O(n**2)", "O(n**2+m**2)"]


# `(n+m)log(n+m)` and `n log n + m log m` are the same function up to a constant
# factor, so a proof landing on either has established the other. Grading treats
# them as one class rather than scoring the label's choice of spelling.
EQUIV = [{"O(n+m)log(n+m)", "O(nlogn+mlogm)"}]


def same_class(a, b):
    """Is `a` the same complexity class as `b`? Tolerant of spelling only."""
    if not a or not b:
        return None
    a, b = canon(a), canon(b)
    if a == b:
        return True
    return any(a in g and b in g for g in EQUIV)


def canon(s):
    """Normalise the ways one class gets written: O(n^2), O(n*n), O(N**2)."""
    s = re.sub(r"\s+", "", str(s)).lower()
    s = s.replace("^", "**").replace("o(", "O(")
    s = s.replace("n*n", "n**2").replace("m*m", "m**2")
    s = s.replace("nlog(n)", "nlogn").replace("log(n)", "logn")
    s = s.replace("log2", "log")
    for k in CLASSES:
        if re.sub(r"\s+", "", k).lower().replace("o(", "O(") == s:
            return k
    return s


# Coarse growth rank, used to give a disagreement a DIRECTION.
#
# A proof establishes an UPPER bound. So `proved O(n**2)` against a label of
# `O(nlogn)` is not a refutation -- an n log n algorithm also satisfies
# steps <= c*n^2, and the proof may simply be loose (an agent charging a seq
# append flatly produces exactly this). Only a bound STRICTLY TIGHTER than the
# label contradicts it, because BigOBench's labels are measured, and so meant
# as the class the program actually is, not merely an upper bound on it.
#
# Ranked with n = m = s, which is why O(n) and O(n+m) share a rank, as do
# O(n*m) and O(n**2).
RANK = {
    "O(1)": 0,
    "O(logn)": 1,
    "O(n)": 2, "O(n+m)": 2,
    "O(nlogn)": 3, "O(n+mlogm)": 3, "O(nlogn+mlogm)": 3, "O(n+m)log(n+m)": 3,
    "O(n*m)": 4, "O(n**2)": 4, "O(n**2+m**2)": 4,
}


def direction(proved, label):
    """How a proved bound stands against a claimed class.

    'tighter'      -- provably cheaper than claimed: refutes the label.
    'looser'       -- consistent with the label; the proof carries no news.
    'same-rank'    -- same growth rank, different spelling of the variables.
    'equal'        -- the same class.
    None           -- one side is missing or unclassified.
    """
    if not proved or not label or proved == "unclassified":
        return None
    if same_class(proved, label):
        return "equal"
    a, b = RANK.get(canon(proved)), RANK.get(canon(label))
    if a is None or b is None:
        return None
    return "tighter" if a < b else ("looser" if a > b else "same-rank")


def _lg(x):
    return max(1.0, math.ceil(math.log2(max(2.0, x))))


def extract_ensures(text):
    """The `ensures steps <= ...` on Solve. Returns the RHS, or None.

    Takes the LAST such clause on `Solve` specifically -- helper methods carry
    their own `steps` bounds and those are not the claim being graded.
    """
    m = re.search(r"method\s+Solve\b", text)
    if not m:
        return None
    tail = text[m.end():]
    body = tail.split("\n{", 1)[0]
    hits = re.findall(r"ensures\s+steps\s*<=\s*(.+)", body)
    return hits[-1].split("//")[0].strip() if hits else None


def to_python(expr):
    """Dafny expression -> Python expression over atom names. (code, atoms)."""
    e = expr.strip().rstrip(";")
    e = re.sub(r"\|\s*([A-Za-z_]\w*)\s*\|", r"L_\1", e)          # |xs|
    e = re.sub(r"\b([A-Za-z_]\w*)\s*\.\s*Length\b", r"L_\1", e)  # xs.Length
    e = re.sub(r"\bCeilLog2\s*\(", "LG(", e)
    e = re.sub(r"\bLog2\s*\(", "LG(", e)
    # any surviving call becomes one opaque size atom: SumLen(numbers) -> F_SumLen_numbers
    def call(m):
        return "F_%s_%s" % (m.group(1), re.sub(r"\W", "", m.group(2)))
    for _ in range(4):
        new = re.sub(r"\b(?!LG\b)([A-Za-z_]\w*)\s*\(([^()]*)\)", call, e)
        if new == e:
            break
        e = new
    if re.search(r"[^\w\s+\-*/()%.,]|\bLG\b(?!\s*\()", e.replace("LG(", "LG (")):
        pass  # tolerated; eval below is the real check
    atoms = sorted({a for a in re.findall(r"\b[A-Za-z_]\w*\b", e)
                    if a not in ("LG",)})
    return e, atoms


def evaluate(code, atoms, vals):
    env = {"LG": _lg, **{a: float(v) for a, v in zip(atoms, vals)}}
    try:
        return float(eval(code, {"__builtins__": {}}, env))
    except Exception:
        return None


def classify(expr):
    """(class, shape, detail). class is a CLASSES entry or 'unclassified'."""
    code, atoms = to_python(expr)
    if not atoms:
        return "O(1)", "1", {"atoms": []}
    if evaluate(code, atoms, [4.0] * len(atoms)) is None:
        return "unclassified", "?", {"atoms": atoms, "why": "eval failed"}

    # Wide, and starting well past the constants: separating n from n log n
    # needs enough decades that lg n itself moves by more than the tolerance.
    SCALES = [256, 4096, 65536, 1048576]
    BASE = 4.0

    def probe(assign, arity):
        """Points to test the ratio at. One-role candidates vary one scale only;
        holding a role at BASE while the other grows is what separates a sum
        from a product, so two-role candidates need all three scalings."""
        shapes = [(1, 1)] if arity == 1 else [(1, 1), (1, 0), (0, 1)]
        pts = []
        for s in SCALES:
            for kn, km in shapes:
                ns, ms = (s if kn else BASE), (s if km else BASE)
                vals = [ns if assign.get(a) == "n" else
                        ms if assign.get(a) == "m" else BASE for a in atoms]
                f = evaluate(code, atoms, vals)
                if f is None or f <= 0:
                    return None
                pts.append((ns, ms, f))
        return pts

    best = None
    for assign, arity in _splits(atoms):
        pts = probe(assign, arity)
        if pts is None:
            continue
        for name in ORDER:
            cand_arity, g = CAND[name]
            if cand_arity != arity:
                continue
            # Theta allows a different constant along each direction -- it
            # forbids the ratio GROWING with scale. So stability is checked
            # within each scaling separately, never across them. Checking
            # across them reads `n**2 + m**2 + n*m` (constant 20 on the axes,
            # 30 on the diagonal) as a mismatch and collapses it to O(n**2);
            # checking within them keeps n and n log n apart, because there
            # the ratio really does climb with scale.
            groups = {}
            for ns, ms, f in pts:
                groups.setdefault((ns > BASE, ms > BASE), []).append(f / g(ns, ms))
            if any(min(v) <= 0 or max(v) / min(v) > 1.35 for v in groups.values()):
                continue
            best = (name, assign)
            break
        if best:
            break

    shape = _shape(code, atoms)
    if best is None:
        return "unclassified", shape, {"atoms": atoms, "expr": code}
    return best[0], shape, {"atoms": atoms, "assign": best[1]}


def _splits(atoms):
    """Assignments of atoms to the n and m roles.

    Two-role splits are tried first: collapsing two distinct size atoms into one
    role would read `2*|a| + 2*|b| + 3` as linear in a single size, which is the
    exact mistake that made two labels in this corpus wrong.
    """
    out = []
    if len(atoms) >= 2:
        for i in range(1, len(atoms)):
            out.append(({a: ("n" if k < i else "m")
                         for k, a in enumerate(atoms)}, 2))
    out.append(({a: "n" for a in atoms}, 1))
    return out


def _shape(code, atoms):
    """A readable growth shape: per-atom degree, and whether a log rides on it."""
    parts = []
    for a in atoms:
        lo = evaluate(code, atoms, [65536.0 if x == a else 4.0 for x in atoms])
        hi = evaluate(code, atoms, [1048576.0 if x == a else 4.0 for x in atoms])
        if lo is None or hi is None or lo <= 0:
            parts.append(f"{a}:?")
            continue
        d = math.log(hi / lo) / math.log(16.0)
        parts.append(f"{a}^{d:.2f}")
    return " + ".join(parts)


if __name__ == "__main__":
    import sys
    for line in sys.stdin:
        line = line.strip()
        if line:
            c, s, d = classify(line)
            print(f"{c:18} {s:28} {line}")
