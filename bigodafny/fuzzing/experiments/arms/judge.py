"""Blind judging: list the calls the judge must make, then file its answers.

    ../../../.venv/bin/python3 judge.py export --batch 1
    ../../../.venv/bin/python3 judge.py import --batch 1

`export` writes `runs/judge/<batch>/input.jsonl`: each distinct call over the batch's four arms, in
shuffled order, with no arm named. A call is one of:

- `bound`: an audited proof's bound, to compare with `truth` (`JUDGE.md` gives the rule);
- `class`: a `class` or `guess` that differs from `truth` as a string, to check for the same class.

The same call from several arms is one item. `key.jsonl` beside it maps each item back to its arms;
the judge does not read it. `import` reads the judge's `output.jsonl` and appends to
`runs/judged.jsonl` one line per arm and row.
"""
from __future__ import annotations
import argparse, json, random

from setup import ARMS, read_jsonl
from report import RUNS


def calls(rec):
    """(kind, value, field) for each call REC needs."""
    if rec["outcome"] == "proved":
        yield "bound", rec["bound"], "tight"
    for field, key in (("class_ok", "class"), ("guess_ok", "guess")):
        if rec.get(key) and rec[key] != rec["truth"]:
            yield "class", rec[key], field


def export(batch, out):
    items = {}                                              # (sid, kind, value) -> [(arm, field)]
    for path in sorted(RUNS.glob(f"*/{batch}/traj.jsonl")):
        for rec in read_jsonl(path):
            for kind, value, field in calls(rec):
                items.setdefault((rec["sid"], kind, value), []).append((rec["arm"], field))
    rows = {e["sid"]: e for e in read_jsonl(ARMS / "manifest.jsonl")}
    keys = list(items)
    random.Random(f"judge-{batch}").shuffle(keys)
    out.mkdir(parents=True, exist_ok=True)
    with (out / "input.jsonl").open("w") as inp, (out / "key.jsonl").open("w") as key:
        for i, (sid, kind, value) in enumerate(keys, 1):
            item = f"{batch}-{i:03d}"
            inp.write(json.dumps({"item": item, "kind": kind, "sid": sid, "row": rows[sid]["path"],
                                  "truth": rows[sid]["truth"], "value": value}) + "\n")
            key.write(json.dumps({"item": item, "sid": sid, "arms": items[(sid, kind, value)]}) + "\n")
    print(f"{len(keys)} items -> {out / 'input.jsonl'}")


def import_(out):
    key = {k["item"]: k for k in read_jsonl(out / "key.jsonl")}
    answers = {a["item"]: a for a in read_jsonl(out / "output.jsonl")}
    if missing := sorted(set(key) - set(answers)):
        raise SystemExit(f"no answer for {missing}")
    judged = {}
    for item, k in key.items():
        a = answers[item]
        for arm, field in k["arms"]:
            line = judged.setdefault((arm, k["sid"]), {"arm": arm, "sid": k["sid"], "reason": []})
            line[field] = a["relation"] != "looser" if field == "tight" else a["same"]
            line["reason"].append(f"{item}: {a['reason']}")
    with (RUNS / "judged.jsonl").open("a") as fh:
        for line in judged.values():
            fh.write(json.dumps({**line, "reason": "; ".join(line["reason"])}, sort_keys=True) + "\n")
    print(f"{len(judged)} lines -> {RUNS / 'judged.jsonl'}")


def main():
    parser = argparse.ArgumentParser(prog="judge.py")
    parser.add_argument("cmd", choices=("export", "import"))
    parser.add_argument("--batch", required=True)
    args = parser.parse_args()
    out = RUNS / "judge" / args.batch
    export(args.batch, out) if args.cmd == "export" else import_(out)


if __name__ == "__main__":
    main()
