# Wave 5, batches 2-4

60 rows, `1675_29` .. `2015_168`. Batch 1 still running.

| batch | agent | audit | tokens | tool calls |
|---|---|---|---|---|
| 2 | 20/20 | **20/20** | 95k | 60 |
| 3 | 20/20 | **20/20** | 107k | 54 |
| 4 | 18/20 | **18/20** | 109k | 69 |

## The finding: a defect the validator cannot see

Batch 3 reimplemented `1861_28` using `1861_16`'s DP instead of transliterating
its combinatorial approach. Every test passed.

It is still wrong. Problem 1861's two rows exist *because* their complexity
differs -- `1861_16` is O(n), `1861_28` is O(n**2). The Dafny became an O(h*w)
DP carrying an O(n**2) label. Since every row's reason for existing is the label
BigOBench measured on *that* Python, substituting the algorithm makes the label
false while leaving the tests green.

Reverted to a stub. Rule now recorded in `CLAUDE.md`: match the source's
asymptotic shape; restructuring inside a complexity class is fine, replacing the
algorithm is not. Where two solutions of one problem seem to want the same code,
that is the cue to check their labels.

Behaviour-equivalence testing cannot detect this. Only reading the diff can.

## Second harness limit found

`1950_45` and `1950_47` declare `Solve(coefficient: real, exponent: int)` and
their tests carry ~100-significant-digit decimals. `Input.from_str` puts them
through Python `float()` before Dafny sees anything:

    4.6329496401734172195e50  ->  4.632949640173417e50

No implementation can pass. `dataset.py` now treats a lossy `real` round-trip as
`unvalidatable`, alongside the parser that raises. Exactly 2 rows qualify,
measured. Splits: strict 534, loose 100, unvalidatable 6.

The agent diagnosed this itself and stopped rather than burning budget — the
right call, and the first time an agent has correctly identified scaffolding as
the cause instead of grinding.

## Note

`decreases *` on both loop and enclosing method reliably sidesteps termination
friction on data-dependent loops; used in 6 of batch 4's rows. Sound here
because the gate is tests, not verification.
