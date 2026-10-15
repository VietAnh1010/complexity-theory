"""Search for the inputs that make a proof copy count the most steps, per size.

A proof's bound is an upper bound over every input the `requires` allow; the
stored tests show what typical inputs cost. This looks for the worst ones: for
each size, the input with the largest `steps`, as `steptrace.py` counts them.

Size is a measurement, a Python expression over the parsed `Input` named `i`
(`--measure "len(i.a_list)"`). The default sums the sizes a label may name:
each list's or string's length, and the value of each int that is not a length.

The search is MAP-Elites. Sizes fall in half-octave buckets; each bucket keeps
its costliest input. A step picks an elite, mutates its fields (type-directed:
grow, shrink, sort, reverse, fill, nudge a value), restores the length
relations the stored tests show (`n == len(a)`), and keeps the child if it
beats its bucket. Element values stay within the range the stored tests use,
so an input stays near the problem's limits without knowing them.

A child counts only if its text parses back to the same `Input`, it passes the
problem's quoted limits (`data/constraints.jsonl`), and Solve's compiled
`requires` accepts it.
"""
from __future__ import annotations
import argparse, copy, dataclasses, math, random, re, sys, time
from collections import defaultdict

from steptrace import Runner  # first: it puts bigodafny/ on sys.path
from common import OUT, _in_spec, log, write_json


# --- shape of the input, learned from the stored tests ----------------------

def walk(v, path, pools):
    """Record leaf values per path: ints' range, strings' alphabet and length."""
    if isinstance(v, bool):
        return
    if isinstance(v, int):
        pools[path].append(v)
    elif isinstance(v, str):
        pools[path + "#len"].append(len(v))
        pools[path + "#chars"].extend(v)
    elif isinstance(v, (list, tuple)):
        if isinstance(v, list):
            pools[path + "#len"].append(len(v))
        for k, x in enumerate(v):
            walk(x, path + ("[]" if isinstance(v, list) else f".{k}"), pools)


def sized(v):
    return isinstance(v, (str, list))


INT = re.compile(r"-?\d+")
INTS = re.compile(r"-?\d+( -?\d+)*")


class Shape:
    def __init__(self, seeds):
        self.fields = [f.name for f in dataclasses.fields(seeds[0])]
        # A str field that always holds integer tokens is mutated as an int
        # (one token) or a list of ints; mutating its characters breaks it.
        self.views = {}
        for f in self.fields:
            vs = [getattr(s, f) for s in seeds]
            if all(isinstance(v, str) for v in vs):
                if all(INT.fullmatch(v) for v in vs):
                    self.views[f] = "int"
                elif all(INTS.fullmatch(v) for v in vs):
                    self.views[f] = "ints"
        self.pools = defaultdict(list)
        for s in seeds:
            for f in self.fields:
                walk(self.get(s, f), f, self.pools)
        self.ties = self._ties(seeds)
        self.linked = self._linked(seeds)

    def get(self, i, f):
        v = getattr(i, f)
        if self.views.get(f) == "int":
            return int(v)
        if self.views.get(f) == "ints":
            return [int(x) for x in v.split(" ")]
        return v

    def set(self, i, f, v):
        if f in self.views:
            v = str(v) if self.views[f] == "int" else " ".join(map(str, v))
        setattr(i, f, v)

    def _ties(self, seeds):
        """int field -> (container field, depth, offset): it always equals that
        length plus offset. Depth 0 is len(c); depth 1 is len(c[0]) for a
        rectangular c. An offset covers a parser's sentinel (`[0] + a_list`)."""
        ties = {}
        for f in self.fields:
            if not all(type(self.get(s, f)) is int for s in seeds):
                continue
            for g in self.fields:
                for depth in (0, 1):
                    lens = [self._len(self.get(s, g), depth) for s in seeds]
                    if None in lens or len(set(lens)) < 2:
                        continue
                    offs = {self.get(s, f) - n for s, n in zip(seeds, lens)}
                    if len(offs) == 1 and abs(next(iter(offs))) <= 2:
                        ties.setdefault(f, (g, depth, offs.pop()))
        return ties

    def _linked(self, seeds):
        """Groups of containers whose lengths are always equal."""
        cs = [f for f in self.fields if all(sized(self.get(s, f)) for s in seeds)]
        groups = []
        for f in cs:
            for grp in groups:
                if all(len(self.get(s, f)) == len(self.get(s, grp[0])) for s in seeds):
                    grp.append(f)
                    break
            else:
                groups.append([f])
        return [g for g in groups if len(g) > 1]

    @staticmethod
    def _len(v, depth):
        if not sized(v):
            return None
        if depth == 0:
            return len(v)
        if not v or not all(sized(x) for x in v):
            return None
        ls = {len(x) for x in v}
        return ls.pop() if len(ls) == 1 else None

    def default_measure(self, i):
        tot = 0
        for f in self.fields:
            v = self.get(i, f)
            if f in self.ties or isinstance(v, bool):
                continue
            tot += size(v)
        return tot

    # --- mutation -------------------------------------------------------

    def leaf_int(self, path, rng):
        p = self.pools.get(path)
        if not p:
            return rng.randint(0, 10)
        lo, hi = min(p), max(p)
        return rng.choice([lo, hi, rng.randint(lo, hi), rng.choice(p)])

    def leaf_str(self, path, rng):
        chars = self.pools.get(path + "#chars") or list("ab")
        lens = self.pools.get(path + "#len") or [1]
        return "".join(rng.choice(chars) for _ in range(rng.choice(lens)))

    def fresh(self, like, path, rng):
        """A new value shaped like `like`, drawn from the pools at `path`."""
        if isinstance(like, bool):
            return rng.random() < 0.5
        if isinstance(like, int):
            return self.leaf_int(path, rng)
        if isinstance(like, str):
            return self.leaf_str(path, rng)
        if isinstance(like, tuple):
            return tuple(self.fresh(x, f"{path}.{k}", rng) for k, x in enumerate(like))
        if isinstance(like, list):
            return [self.mutate(copy.deepcopy(x), path + "[]", rng) for x in like]
        return like

    def mutate(self, v, path, rng):
        if isinstance(v, bool):
            return not v
        if isinstance(v, int):
            p = self.pools.get(path) or [0, 10]
            lo, hi = min(p), max(p)
            op = rng.randrange(5)
            w = [v + 1, v - 1, v * 2, v // 2, self.leaf_int(path, rng)][op]
            return min(max(w, lo), hi)
        if isinstance(v, tuple):
            if not v:
                return v
            k = rng.randrange(len(v))
            return v[:k] + (self.mutate(v[k], f"{path}.{k}", rng),) + v[k + 1:]
        if isinstance(v, str):
            chars = self.pools.get(path + "#chars") or list("ab")
            return "".join(self._seq_op(list(v), path, rng,
                                        lambda: rng.choice(chars), lambda c: rng.choice(chars)))
        if isinstance(v, list):
            if v and all(isinstance(x, (list, str)) for x in v) and rng.random() < 0.3:
                return self._column_op(v, path, rng)
            return self._seq_op(v, path, rng,
                                lambda: (self.fresh(rng.choice(v), path + "[]", rng) if v else 0),
                                lambda x: self.mutate(x, path + "[]", rng))
        return v

    def _seq_op(self, v, path, rng, new, mut):
        n = len(v)
        cap = max(self.pools.get(path + "#len") or [n])
        op = rng.choice(["elem", "elem", "insert", "delete", "double", "halve",
                         "sort", "rsort", "reverse", "fill", "shuffle"])
        try:
            if op == "elem" and n:
                k = rng.randrange(n); v[k] = mut(v[k])
            elif op == "insert" and n < cap:
                v.insert(rng.randrange(n + 1), new())
            elif op == "delete" and n > 1:
                del v[rng.randrange(n)]
            elif op == "double" and n:
                v = (v + [mut(x) for x in v])[:cap]
            elif op == "halve" and n > 1:
                v = v[: n // 2]
            elif op == "sort":
                v = sorted(v)
            elif op == "rsort":
                v = sorted(v, reverse=True)
            elif op == "reverse":
                v = v[::-1]
            elif op == "fill" and n:
                v = [copy.deepcopy(v[rng.randrange(n)]) for _ in v]
            elif op == "shuffle":
                rng.shuffle(v)
        except TypeError:               # unorderable elements
            pass
        return v

    def _column_op(self, rows, path, rng):
        """Grow or shrink every row of a rectangular container together."""
        if rng.random() < 0.5:
            return [r[:-1] if len(r) > 1 else r for r in rows]
        return [r + r[-1:] if r else r for r in rows]

    def repair(self, i, changed, rng):
        """Restore linked lengths and tied ints after `changed` was mutated."""
        for grp in self.linked:
            if changed in grp:
                n = len(self.get(i, changed))
                for g in grp:
                    if g != changed:
                        self.set(i, g, self._resize(self.get(i, g), n, g, rng))
        for f, (g, depth, off) in self.ties.items():
            n = self._len(self.get(i, g), depth)
            if n is not None:
                self.set(i, f, n + off)
        return i

    def _resize(self, v, n, path, rng):
        if len(v) >= n:
            return v[:n]
        if isinstance(v, str):
            chars = self.pools.get(path + "#chars") or list("ab")
            return v + "".join(rng.choice(chars) for _ in range(n - len(v)))
        return v + [self.fresh(rng.choice(v), path + "[]", rng) if v else 0
                    for _ in range(n - len(v))]


def size(v, top=True):
    """A list's or string's length; an int's value only at top level. A list
    of containers counts their elements, so a grid's size is its cell count."""
    if isinstance(v, bool):
        return 0
    if isinstance(v, int):
        return abs(v) if top else 0
    if isinstance(v, str):
        return len(v)
    if isinstance(v, tuple):
        return sum(size(x, False) for x in v)
    if isinstance(v, list):
        return sum(max(1, size(x, False)) for x in v)
    return 0


# --- growth fit ------------------------------------------------------------

CLASSES = {
    "O(1)": lambda m: 1.0,
    "O(logn)": lambda m: math.log2(m + 1),
    "O(n)": lambda m: m,
    "O(nlogn)": lambda m: m * math.log2(m + 1),
    "O(n**2)": lambda m: m * m,
    "O(n**3)": lambda m: m ** 3,
}


def fit(points):
    """Classes ranked by relative error of steps ~ c*f(m) + d, least squares."""
    pts = [(m, s) for m, s in points if m >= 1]
    if len(pts) < 3:
        return []
    out = []
    for name, f in CLASSES.items():
        xs = [f(m) for m, _ in pts]
        ys = [s for _, s in pts]
        n = len(xs)
        mx, my = sum(xs) / n, sum(ys) / n
        vx = sum((x - mx) ** 2 for x in xs)
        c = 0.0 if vx == 0 else sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / vx
        if c < 0:
            continue
        d = my - c * mx
        err = math.sqrt(sum(((c * x + d) - y) ** 2 for x, y in zip(xs, ys)) / n)
        out.append({"class": name, "c": c, "rel_rmse": err / max(my, 1)})
    return sorted(out, key=lambda r: r["rel_rmse"])


# --- search ----------------------------------------------------------------

def bucket(m, res):
    return int(math.floor(math.log2(m + 1) * res))


def fuzz(sid, measure=None, iters=2000, seconds=None, res=2, seed=0, timeout=5):
    rng = random.Random(seed)
    r = Runner(sid)
    for n in r.notes:
        log(f"{sid}: {n}")
    parsed = []
    ns = {}
    exec(compile(r.task["dataclass_code"], "dataclass", "exec"), ns)
    Input = ns["Input"]
    for text in r.seeds():
        try:
            parsed.append((text, Input.from_str(text)))
        except Exception:
            pass
    if not parsed:
        raise SystemExit(f"{sid}: no parseable seed input")
    shape = Shape([p for _, p in parsed])
    meas = (lambda i: shape.default_measure(i)) if measure is None else \
        (lambda i: eval(measure, {"len": len, "max": max, "sum": sum, "abs": abs}, {"i": i}))
    max_m = max(meas(p) for _, p in parsed)
    log(f"{sid}: {len(parsed)} seeds, ties {shape.ties}, linked {shape.linked}, "
        f"max measure {max_m}")

    archive = {}                     # bucket -> elite
    seeds_best = {}
    stats = defaultdict(int)

    def consider(text, i, origin):
        m = meas(i)
        if m > max_m:
            stats["over_max"] += 1
            return
        if not _in_spec(r.task, text):
            stats["out_of_spec"] += 1
            return
        out = r.run(text, timeout=timeout)
        stats[out["status"]] += 1
        if out["status"] != "ok":
            return
        b = bucket(m, res)
        e = {"measure": m, "steps": out["steps"], "input": text, "origin": origin}
        if origin == "seed" and seeds_best.get(b, {}).get("steps", -1) < e["steps"]:
            seeds_best[b] = e
        cur = archive.get(b)
        if cur is None or (e["steps"], -m) > (cur["steps"], -cur["measure"]):
            archive[b] = e
            if origin != "seed":
                stats["improved"] += 1

    for text, i in parsed:
        consider(text, i, "seed")
    t0 = time.time()
    for it in range(iters):
        if seconds and time.time() - t0 > seconds:
            break
        if not archive:
            break
        parent = archive[rng.choice(list(archive))]
        child = Input.from_str(parent["input"])
        for _ in range(rng.choice([1, 1, 2, 3])):
            f = rng.choice(shape.fields)
            if f in shape.ties:
                continue
            shape.set(child, f, shape.mutate(copy.deepcopy(shape.get(child, f)), f, rng))
            child = shape.repair(child, f, rng)
        text = repr(child)
        try:
            back = Input.from_str(text)
            same = repr(back) == text
        except Exception:
            same = False
        if not same:
            stats["no_round_trip"] += 1
            continue
        consider(text, back, "fuzz")
    r.close()

    elites = sorted(archive.values(), key=lambda e: e["measure"])
    seeds = sorted(seeds_best.values(), key=lambda e: e["measure"])
    return {
        "solution_id": sid, "label": r.task["time_complexity_inferred"],
        "measure": measure or "default: sizes a label may name", "max_measure": max_m,
        "iters": it + 1, "seconds": round(time.time() - t0, 1), "stats": dict(stats),
        "ties": {k: list(v) for k, v in shape.ties.items()}, "linked": shape.linked,
        "fit_fuzz": fit([(e["measure"], e["steps"]) for e in elites])[:3],
        "fit_seeds": fit([(e["measure"], e["steps"]) for e in seeds])[:3],
        "elites": elites, "seed_best": seeds,
    }


def main(argv=None):
    ap = argparse.ArgumentParser(prog="stepfuzz.py")
    ap.add_argument("sid")
    ap.add_argument("--measure", help="size expression over the parsed Input `i`")
    ap.add_argument("--iters", type=int, default=2000)
    ap.add_argument("--seconds", type=float)
    ap.add_argument("--res", type=int, default=2, help="buckets per doubling of size")
    ap.add_argument("--seed", type=int, default=0)
    a = ap.parse_args(argv)
    rep = fuzz(a.sid, a.measure, a.iters, a.seconds, a.res, a.seed)
    seed_by = {bucket(e["measure"], a.res): e for e in rep["seed_best"]}
    print(f"{a.sid}  label {rep['label']}  measure: {rep['measure']}")
    print(f"{'size':>8} {'seed steps':>11} {'fuzz steps':>11} {'gain':>6}")
    for e in rep["elites"]:
        s = seed_by.get(bucket(e["measure"], a.res))
        gain = f"{e['steps'] / s['steps']:.2f}" if s and s["steps"] else "-"
        print(f"{e['measure']:>8} {s['steps'] if s else '-':>11} {e['steps']:>11} {gain:>6}"
              f"  {'*' if e['origin'] == 'fuzz' else ''}")
    for k in ("fit_seeds", "fit_fuzz"):
        print(k, ", ".join(f"{f['class']} ({f['rel_rmse']:.2f})" for f in rep[k]))
    print("stats", rep["stats"])
    write_json(OUT / "fuzz" / f"{a.sid}.json", rep)
    log(f"-> out/fuzz/{a.sid}.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
