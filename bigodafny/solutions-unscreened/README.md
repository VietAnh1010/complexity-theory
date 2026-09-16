# `solutions-unscreened/` — quarantined before the label audit ran

127 rows. Behaviour is gated exactly as in `solutions/` — these pass their
tests. What they have never had is a **label screening**: the audit that
produced `solutions-disputed/` covered 506 rows (`solutions/` plus what became
the disputed queue) and did not include these.

So the name is a statement about process, not about the code. "Not screened"
is not "wrong", and it is not "right" either. It is unknown.

> Renamed from `solutions-inexact/`. "Inexact" read as a claim about numeric
> precision, which was never what it meant.

## Why each row was pulled out

Two screens ran before the audit existed, and both were coarse:

- **Sibling convergence** — 12 rows, recorded in `data/quarantine.jsonl` and
  surfaced as `quarantine_reasons` in `data/dataset.jsonl`. Two solutions of
  one problem carry different labels but converged to near-identical Dafny.
  At least one of the two must be mislabelled, or one translation replaced the
  other's algorithm. `siblings.py` finds them; it does not say which is at
  fault.
- **Container use** — 22 rows use `set<T>`, 11 use `map<K,V>`. These were
  pulled when the cost model was read off the Dafny Python backend, where both
  copy on write and turn a linear loop quadratic.

**The second screen no longer justifies a quarantine.** `batches/cost-axioms/PLAN.md`
charges set insertion and map update O(1) by stipulation, so a row is no longer
suspect merely for using them. Those rows are candidates to rejoin `solutions/`
after a proper screening — they have not been screened, so they have not moved.

## What to do with this directory

Run the label audit over it. `labelaudit.py evidence --prefix unscreened` emits
batches in the same shape the audit used, and `batches/labelaudit/PROMPT.md` is
the agent prompt. Each row then either joins `solutions/` or joins
`solutions-disputed/` with a verdict, and this directory empties.

Until then every gate still runs on these rows and they stay in
`data/dataset.jsonl` with their labels. Quarantined, not deleted.
