# Prove two rows that the value-versus-size convention unblocks

Read `PROMPT.md` in this directory first — the shape, the charges, the rules
about `assume`, `decreases *`, and never editing `solutions/` all still apply.
This file states only what is different.

## What changed

**Decided 2026-09-17: a loop bounded by an input VALUE counts.** The value is a
parameter of the bound, not a constant. `COMPLEXITY.md` § 1 "Value is a
parameter, not a constant" is the authority.

So a bound may name an input value. `O(r)` for `while i < r`, `O(log v)` for a
binary search over `v`, `O(L)` for a per-character string comparison — all legal
bounds now, where before they would have been pushed into a constant.

## Your two rows

Both were recorded `unresolved / structural-unbounded` in the campaign,
meaning no bound in `n` alone existed. That blocker is gone.

**`solutions/2128/2128_34.dfy`** — label `O(n**2)`. The array is sized `r+1`
where `r` starts at `m` and grows by `pos[pi].1`, arbitrary input values. State
the bound in terms of `n` *and* `r`. Note this row deliberately keeps an
`array<T>` for backend reasons; its header says so. Do not convert it to `seq`.

**`solutions/2942/2942_42.dfy`** — label `O(n*m)`. This one is **not** a
value-versus-size case and the convention does not decide it. Its blocker is
that `n`'s sign is unconstrained, so `invariant i <= n` fails at `n < 0`. Bound
it with `max(0, n)` instead — `solutions-proved/2012/2012_399.dfy` already does
exactly this, with `8 * (if n > 0 then n else 0) + 4`. Read it first.

Do **not** add a `requires` to either row to dodge the problem.

## Budget

**4 attempts and 10 minutes per row** — wider than the campaign's 3 and 5,
because these two provably could not close under the old convention and are
fresh attempts, not retries.

## Output

Append one record per row to `traj_convention.jsonl` here, same schema as
`traj_a.jsonl`. On `unresolved`, `why_failed` names the obstacle in one
sentence.

Be concise. Final message at most 6 lines.
