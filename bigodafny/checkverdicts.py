"""Reject a malformed label-audit batch before anyone reads its conclusions.

A cheap auditor produced `true_class` values of "1", "n2" and "n+m_variant",
`cause: "translation"` on a row with no loops (where translation cannot be the
cause), and three-word evidence strings. None of that is visible in a summary --
the batch reports "6 mismatches" either way. So the schema is checked
mechanically, and a batch that fails does not get read.

This is a gate, not a formatter: it never repairs a verdict, it only refuses one.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import DATA, log, read_jsonl                          # noqa: E402

CLASSES = {"O(1)", "O(logn)", "O(n)", "O(n**2)", "O(n**2+m**2)", "O(n*m)",
           "O(n+m)", "O(n+m)log(n+m)", "O(n+mlogm)", "O(nlogn)",
           "O(nlogn+mlogm)"}
VERDICTS = {"ok", "mismatch", "unsure"}
CAUSES = {"label", "translation", "both", ""}
CONFIDENCE = {"high", "medium", "low"}
MIN_EVIDENCE_WORDS = 12


def check(path, batch_path=None):
    rows, bad = [], []
    for i, line in enumerate(Path(path).read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            rows.append((i, json.loads(line)))
        except json.JSONDecodeError as e:
            bad.append((i, "?", f"not JSON: {e}"))

    expected = None
    if batch_path and Path(batch_path).exists():
        expected = [r["sid"] for r in json.loads(Path(batch_path).read_text())]

    seen = set()
    for i, r in rows:
        sid = r.get("sid", "?")
        seen.add(sid)
        def err(msg):
            bad.append((i, sid, msg))
        if r.get("verdict") not in VERDICTS:
            err(f"verdict {r.get('verdict')!r} not in {sorted(VERDICTS)}")
        tc = r.get("true_class")
        if tc not in CLASSES:
            err(f"true_class {tc!r} is not one of the 11 label classes")
        if r.get("cause") not in CAUSES:
            err(f"cause {r.get('cause')!r} not in {sorted(CAUSES)}")
        if r.get("confidence") not in CONFIDENCE:
            err(f"confidence {r.get('confidence')!r} not in {sorted(CONFIDENCE)}")
        ev = (r.get("evidence") or "").strip()
        if len(ev.split()) < MIN_EVIDENCE_WORDS:
            err(f"evidence is {len(ev.split())} words; a reviewer cannot check "
                f"a claim that short (min {MIN_EVIDENCE_WORDS})")
        if r.get("verdict") == "mismatch":
            if tc == r.get("label"):
                err("verdict is mismatch but true_class equals the label")
            if not r.get("cause"):
                err("mismatch with no cause")
        if r.get("verdict") == "ok" and tc != r.get("label"):
            err(f"verdict ok but true_class {tc!r} != label {r.get('label')!r}")

    if expected is not None:
        missing = [s for s in expected if s not in seen]
        extra = [s for s in seen if s not in expected]
        if missing:
            bad.append((0, "-", f"{len(missing)} row(s) missing: {missing[:8]}"))
        if extra:
            bad.append((0, "-", f"not in batch: {extra[:8]}"))

    for i, sid, msg in bad:
        log(f"  REJECT line {i} {sid}: {msg}")
    counts = {k: sum(1 for _, r in rows if r.get("verdict") == k) for k in VERDICTS}
    log(f"{Path(path).name}: {len(rows)} verdicts {counts}; "
        f"{len(bad)} schema violation(s)")
    return bad


def oracle(path):
    """Cross-check against rows that carry a machine-checked bound.

    `solutions-verified/` holds proofs, not opinions. A verdict that contradicts
    one is wrong, and it is the cheapest calibration available.
    """
    proofs = {r["solution_id"]: r for r in read_jsonl(DATA / "complexity_proofs.jsonl")}
    hits = []
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        p = proofs.get(r.get("sid"))
        if p:
            hits.append((r, p))
    for r, p in hits:
        log(f"  ORACLE {r['sid']:>10} label={p['label']:<14} "
            f"verdict={r.get('verdict'):<9} true_class={r.get('true_class'):<14} "
            f"proved={p['proved_bound']}")
    log(f"{len(hits)} row(s) overlap a machine-checked proof")
    return hits


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("verdicts")
    ap.add_argument("--batch")
    a = ap.parse_args()
    bad = check(a.verdicts, a.batch)
    oracle(a.verdicts)
    sys.exit(1 if bad else 0)
