"""Partition the 100 examples into agent batches, and say what is left to run.

Batches of 4, dealt round-robin down a difficulty-sorted list, so no single
batch is all-hard: a wave that stalls should stall on one example, not on four.
The partition is written once into `runs/<id>/waves.json` and never recomputed,
so an interrupted run resumes on the same batches it started with.

    python3 experiments/waves.py --run-id RUN --plan          # create/show it
    python3 experiments/waves.py --run-id RUN --todo          # what is unrun
    python3 experiments/waves.py --run-id RUN --wave 3 --arm blind   # its sids
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from stage import CX_ROOT                                          # noqa: E402

HERE = Path(__file__).resolve().parent
RUNS = HERE / "runs"
SIZE = 4


def plan(run_id, exclude=()):
    p = RUNS / run_id / "waves.json"
    if p.exists():
        return json.loads(p.read_text())
    man = json.loads((HERE / "manifest.json").read_text())
    exs = [e for e in man["examples"] if e["sid"] not in exclude]
    exs.sort(key=lambda e: (-e["difficulty_static"], -e["score"]))
    nb = (len(exs) + SIZE - 1) // SIZE
    batches = [[] for _ in range(nb)]
    for i, e in enumerate(exs):
        batches[i % nb].append(e)
    # Easiest first WITHIN a batch. The pilot's labeled agent spent all 62 of
    # its tool calls on the hardest example, which happened to be first, and
    # wrote nothing for the other three. Ordering the other way costs the tail.
    batches = [[e["sid"] for e in sorted(b, key=lambda e: (e["difficulty_static"],
                                                          -e["score"]))]
               for b in batches]
    out = {"size": SIZE, "batches": batches}
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    return out


def done(run_id, arm, sid):
    return (CX_ROOT / run_id / arm / sid / "result.json").exists()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-id", required=True)
    ap.add_argument("--plan", action="store_true")
    ap.add_argument("--todo", action="store_true")
    ap.add_argument("--wave", type=int)
    ap.add_argument("--arm", choices=["labeled", "blind"])
    ap.add_argument("--exclude", nargs="*", default=[])
    a = ap.parse_args()

    pl = plan(a.run_id, set(a.exclude))
    if a.wave is not None:
        print(" ".join(pl["batches"][a.wave]))
        return
    if a.todo:
        for arm in ("labeled", "blind"):
            todo = [i for i, b in enumerate(pl["batches"])
                    if any(not done(a.run_id, arm, s) for s in b)]
            print(f"{arm:8} batches with unfinished examples: "
                  f"{len(todo)}/{len(pl['batches'])}  {todo[:20]}")
        return
    print(f"{len(pl['batches'])} batches of <= {pl['size']}")
    for i, b in enumerate(pl["batches"]):
        print(f"  {i:3}  {' '.join(b)}")


if __name__ == "__main__":
    main()
