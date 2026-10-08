# `solutions-unscreened/` — quarantined before the label audit ran

127 rows. Behaviour is gated exactly as in `solutions/` — these pass their
tests. What they have never had is a **label screening**: the audit that
produced `solutions-disputed/` covered 506 rows (`solutions/` plus what became
the disputed queue) and did not include these.

So the name is a statement about process, not about the code. "Not screened"
is not "wrong", and it is not "right" either. It is unknown.

## Why each row was pulled out

Two coarse screens, both older than the label audit:

- **Sibling convergence** — 12 rows, recorded in `data/quarantine.jsonl` and
  surfaced as `quarantine_reasons` in `data/dataset.jsonl`. Two solutions of
  one problem carry different labels but converged to near-identical Dafny.
  At least one of the two must be mislabelled, or one translation replaced the
  other's algorithm. `label_audit.py siblings` finds them; it does not say which is at
  fault.
- **Container use** — 29 rows use `set<T>` or `map<K,V>` (22 and 11, with an
  overlap). In the Dafny Python backend both copy on write.

**The second screen does not justify a quarantine.** `COMPLEXITY.md` § 1
charges set insertion and map update `1`, so using them makes a row no more
suspect. Those rows are candidates to rejoin `solutions/` once screened.

## What to do with this directory

Run the label audit over it. `label_audit.py evidence --dir solutions-unscreened --prefix unscreened` emits
batches in the same shape the audit used, and `batches/labelaudit/PROMPT.md` is
the agent prompt. Each row then either joins `solutions/` or joins
`solutions-disputed/` with a verdict, and this directory empties.

Until then every gate still runs on these rows and they stay in
`data/dataset.jsonl` with their labels. Quarantined, not deleted.
