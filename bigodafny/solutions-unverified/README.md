# `solutions-unverified/` — behaviour gated, safety not proved

3 rows. They pass their tests like anything in `solutions/`. What `dafny verify`
cannot discharge is the set of obligations the file raises **with no user
specification at all**: a sequence index in range, a divisor non-zero, a
recursion that terminates.

| row | what the verifier will not accept |
|---|---|
| `1336/1336_157.dfy` | function precondition at line 58 |
| `1369/1369_10.dfy` | `decreases` expression might not decrease |
| `1369/1369_14.dfy` | `decreases` expression might not decrease |

Read that as: **safe on the stored tests, unproven for every other input.** The
tests are evidence, not a proof, and the gap is exactly what this directory
names.

"Verified" here means what `dafny verify` means — safety. It does not mean the
complexity label is right. The directory that proves labels is
`solutions-proved/`, and the two are independent: a row can be safety-verified
with an unproved label, or carry a proved label while sitting here.

> This directory keeps its name. Its sibling `solutions-verified/` was renamed
> to `solutions-proved/` precisely because it meant the other thing.

## Getting a row out

`.claude/skills/bigodafny-verify/SKILL.md` is the procedure. In short: add the
weakest `requires` that makes the obligation go through, check it against real
inputs with `precheck.py` (a precondition that excludes inputs the row's own
tests supply is a bug, not a proof), re-run `validate.py`, then
`git mv` the row into `solutions/`.

Two rules that pass are not negotiable: no `assume` may be introduced to close
a gap, and no `decreases *`.
