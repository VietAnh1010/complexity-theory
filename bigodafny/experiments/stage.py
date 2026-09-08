"""Stage the two corpora the experiment agents work in.

Staged **outside the repository**, under the session scratchpad, so that "any
path outside your example directory" is one prefix check the guard hook can
enforce. Nothing here is committed; `manifest.json` plus this script regenerate
it exactly.

The blind corpus is the labeled corpus with the answer removed. What has to go,
measured over `solutions/`: all 506 files carry `// time complexity: O(...)` in
their header, and `problem_name` is a Codeforces title that is itself a recall
handle for the intended solution.

The scrub audit rests on one invariant: **a file that is byte-identical across
every example cannot carry a per-example answer.** GUIDE.md, TASK.md,
RESULT.schema.json and prelude.dfy are constant by construction, asserted here
by `constancy_check`, and therefore exempt. Everything else is scanned.

    python3 experiments/stage.py --run-id pilot1
    python3 experiments/stage.py --run-id pilot1 --check     # audit only
"""
from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import DATA, PRELUDE, read_jsonl                      # noqa: E402
from features import split_file                                   # noqa: E402
from guide import GUIDE                                           # noqa: E402

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "manifest.json"
RUNS = HERE / "runs"

CX_ROOT = Path(os.environ.get(
    "CX_ROOT",
    "/tmp/claude-0/-home-user-complexity-theory/"
    "ed2768b2-16e6-58fb-a2f9-5d0137f30fef/scratchpad/cx-run"))

# Constant across every example, in both arms. Exempt from the leak scan.
CONSTANT = ("GUIDE.md", "TASK.md", "RESULT.schema.json", "prelude.dfy")

SCHEMA = """{
  "sid":            "string  -- the example id, copied from task.dfy",
  "guess":          "string  -- BLIND ARM ONLY. The class you commit to before
                     proving anything, one of the strings listed in GUIDE.md.
                     Write this file with guess filled in and everything else
                     null BEFORE you start the proof, then update it later.",
  "guess_basis":    "string  -- BLIND ARM ONLY. One line: what in the code decided it",
  "bound_ensures":  "string  -- the exact `ensures steps <= ...` you proved, or null",
  "proved_class":   "string  -- the class your bound corresponds to, or null",
  "size_mapping":   "string  -- which arguments of Solve you took to be n and m",
  "verdict":        "string  -- proves | refutes | gave_up",
  "added_requires": "list    -- any `requires` you added to Solve, verbatim",
  "verified":       "bool    -- did `dafny verify` report 0 errors on your final file",
  "notes":          "string  -- <= 4 lines: what was hard, what you charged, what you gave up"
}
"""

TASK_LABELED = """# Your task

`task.dfy` contains a Dafny method `Solve` and, in its header, the cost that is
claimed for it.

1. Read `GUIDE.md`, then `description.md`, `solution.py` and `task.dfy`.
2. Instrument `Solve` with a ghost step counter and prove a bound of the
   claimed shape.
3. If the claim is wrong, prove the bound that is actually true and set
   `verdict` to `refutes`. Do not bend the proof to fit the claim.
4. Write `result.json` following `RESULT.schema.json`.
"""

TASK_BLIND = """# Your task

`task.dfy` contains a Dafny method `Solve`. Its cost is not stated anywhere.

1. Read `GUIDE.md`, then `description.md`, `solution.py` and `task.dfy`.
2. Decide which of the classes listed in `GUIDE.md` this method belongs to.
   Write `result.json` now, with `guess` and `guess_basis` filled in and every
   other field null. Do this BEFORE you attempt any proof.
3. Then instrument `Solve` with a ghost step counter and prove your guess.
4. If the proof forces you to a different bound, keep the original `guess`
   unchanged, record the bound you proved in `proved_class`, and set `verdict`
   to `refutes`.
5. Update `result.json` with the rest of the fields.
"""

HEADER = """// example: {sid}
{extra}//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
{py}
// ----------------------------------------------------------------------
"""

LEAK_RE = re.compile(r"time.?complexity|O\s*\(\s*[nNmMkK1]|Theta\s*\(|"
                     r"\blogn\b|\blog ?n\b|asymptotic", re.I)
REDACTION = "[complexity note redacted for this experiment]"


def redact(text):
    """Strip the author's own complexity comments. Applied to BOTH arms.

    One row of the 100 carries `#Ai += x O(logN)` in its Python. Removing it
    from the blind arm only would make the arms differ in more than the label,
    so it goes from both and the row is recorded as redacted.
    """
    out, hit = [], False
    for line in text.splitlines():
        if LEAK_RE.search(line):
            hit = True
            if "#" in line:
                head, _, _ = line.partition("#")
                line = head + "# " + REDACTION
            else:
                line = REDACTION
        out.append(line)
    return "\n".join(out), hit


def python_comment(code):
    return "\n".join("// " + l for l in code.rstrip().splitlines())


def stage_one(dst: Path, ex, row, arm):
    dst.mkdir(parents=True, exist_ok=True)
    text = Path(ex["path"]).read_text(encoding="utf-8")
    _, body = split_file(text)
    body = body.replace('include "../../prelude.dfy"', 'include "prelude.dfy"')

    py_src, redacted = redact(row["solution_code"])
    extra = ("// problem: %s\n// claimed time complexity: %s\n"
             % (row["problem_name"], ex["label"])) if arm == "labeled" else ""
    head = HEADER.format(sid=ex["sid"], extra=extra, py=python_comment(py_src))

    (dst / "task.dfy").write_text(head + "\n" + body, encoding="utf-8")
    (dst / ".original.dfy").write_text(head + "\n" + body, encoding="utf-8")
    (dst / "solution.py").write_text(py_src, encoding="utf-8")
    (dst / "description.md").write_text(row["description"], encoding="utf-8")
    (dst / "GUIDE.md").write_text(GUIDE, encoding="utf-8")
    (dst / "TASK.md").write_text(
        TASK_LABELED if arm == "labeled" else TASK_BLIND, encoding="utf-8")
    (dst / "RESULT.schema.json").write_text(SCHEMA, encoding="utf-8")
    shutil.copyfile(PRELUDE, dst / "prelude.dfy")
    return redacted


def scrub_check(root: Path, ex, row):
    """Every way the answer could still be sitting in a blind example."""
    bad = []
    for p in sorted(root.rglob("*")):
        if not p.is_file() or p.name in CONSTANT:
            continue
        t = p.read_text(encoding="utf-8", errors="replace")
        for m in LEAK_RE.finditer(t):
            ln = t[:m.start()].count("\n")
            bad.append(f"{p.name}:{ln+1}: {t.splitlines()[ln].strip()[:80]}")
        if row["problem_name"] and row["problem_name"] in t:
            bad.append(f"{p.name}: problem name present")
        if ex["label"] in t:
            bad.append(f"{p.name}: LABEL PRESENT")
    return bad


def constancy_check(run: Path, arm):
    """The exemption above is only valid if the exempt files really are equal."""
    bad, seen = [], {}
    for d in sorted((run / arm).iterdir()):
        for name in CONSTANT:
            h = hashlib.sha256((d / name).read_bytes()).hexdigest()
            if name in seen and seen[name][0] != h:
                bad.append(f"{arm}/{d.name}/{name} differs from {seen[name][1]}")
            seen.setdefault(name, (h, d.name))
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-id", required=True)
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args()

    man = json.loads(MANIFEST.read_text())
    rows = {r["solution_id"]: r for r in read_jsonl(DATA / "tasks.jsonl")}
    exs = man["examples"]
    if a.only:
        keep = set(a.only)
        exs = [e for e in exs if e["sid"] in keep]

    run = CX_ROOT / a.run_id
    problems, redacted = [], []
    for e in exs:
        row = rows[e["sid"]]
        for arm in ("labeled", "blind"):
            d = run / arm / e["sid"]
            if not a.check:
                if stage_one(d, e, row, arm) and arm == "blind":
                    redacted.append(e["sid"])
        for b in scrub_check(run / "blind" / e["sid"], e, row):
            problems.append(f"{e['sid']}: {b}")
    problems += constancy_check(run, "blind")

    (RUNS / a.run_id).mkdir(parents=True, exist_ok=True)
    (RUNS / a.run_id / "staged.json").write_text(json.dumps(
        {"run_id": a.run_id, "root": str(run), "redacted": sorted(redacted),
         "sids": [e["sid"] for e in exs]}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")

    print(f"root:      {run}")
    print(f"staged:    {len(exs)} examples x 2 arms")
    print(f"redacted:  {len(redacted)} {sorted(redacted)}")
    if problems:
        print(f"\nSCRUB FAILURES: {len(problems)}")
        for p in problems[:40]:
            print("  " + p)
        sys.exit(1)
    print("scrub:     clean (task.dfy, solution.py, description.md, .original.dfy)")


if __name__ == "__main__":
    main()
