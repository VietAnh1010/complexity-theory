# Campaign configuration: what the pooled numbers mean

Seven proof campaigns ran between 2026-09-16 and 2026-09-23. Each drew 50 rows
except campaign 5, which has 48 counted rows after two already-proved rows were
removed. The campaigns did not use one fixed configuration, so their pooled
numbers need context.

| campaign | date | draw |
|---|---|---:|
| `prove-sample` | 2026-09-16 | 50 |
| `prove-sample-2` | 2026-09-21 | 50 |
| `prove-sample-3` | 2026-09-21 | 50 |
| `prove-sample-4` | 2026-09-21 | 50 |
| `prove-sample-5` | 2026-09-22 | 48 counted |
| `prove-sample-6` | 2026-09-23 | 50 |
| `prove-sample-7` | 2026-09-23 | 50 |

## Differences that matter

- Campaigns 1–7 all charged sequence updates as one unit.
- The value-versus-size rule was added in campaign 2: input values remain
  parameters of a bound.
- The `tighter-costmodel` and `tighter-translation` relations were added in
  campaign 3.
- `IntToString` became a one-unit operation in campaigns 6 and 7.
- Campaign 7 is the first fresh-only draw (`--exclude-drawn`) and the first to
  request `reads` traces. The rule was added during the run; the 30 rows that
  finished without one were rerun on 2026-09-24 with the newer prelude, so all
  50 have traces but two configurations are mixed. Its README separates them.

## How to compare campaigns

Plain draws increasingly re-selected rows that had already failed. Their raw
rates therefore fell from 84% in campaign 1 to 60% in campaign 6 even though
the agent budget did not change. Compare fresh-row rates, or compare campaign 7
with campaign 1; do not read the raw sequence as a learning curve.

Proof bounds were also normalised after `proofs.py` changed on 2026-09-22.
Older records preserve the agent's original result; current files may contain a
later hand-tightened proof. The two should not be mixed in one rate.

## Reading campaign records

The campaign README gives the bounded-agent result. `old_record.jsonl` keeps
superseded versions. A later proof or changed relation does not rewrite what the
agent achieved under its budget. `data/prove_stats.md` is the generated summary;
use it for current totals and the README for experimental caveats.
