# Verification sweep

`dafny verify` run on all 452 translations. No pre/postconditions needed:
indexing a `seq`, dividing, and terminating are each a proof obligation Dafny
raises on its own.

**143 of 452 verify (32%).**

| directory | verified | total | rate |
|---|---|---|---|
| `solutions/` | 111 | 346 | 32% |
| `solutions-inexact/` | 32 | 106 | 30% |

The two rates match, so this is independent of the sibling/set quarantine.

## What fails

| obligation | rows |
|---|---|
| index out of range | 240 |
| precondition (mostly `FloorDiv`'s `b != 0`) | 25 |
| termination / `decreases` | 14 |
| other (bounds, postcondition, verifier timeout) | 14 |
| division by zero | 11 |
| map domain | 3 |
| negative seq size, subset constraint | 2 |

## What this means

Not a failing test. Every one of these 309 rows passes every stored test, and a
spot-check of 25 after the move confirms behaviour is unchanged.

It means the translation is unproven outside the tested inputs. `a[i]` where
Dafny cannot show `i < |a|` will fault on some input; the stored tests just do
not contain it. Python raises `IndexError` where Dafny's compiled code has
undefined behaviour, so the Python original was never under the same obligation.

This is the same shape as every other finding in this project: the test gate
answers a narrower question than it appears to.

## Directory meaning

    solutions/             valid AND safety-verified          111
    solutions-unverified/  valid, safety obligations open     235
    solutions-inexact/     complexity label suspect           106
    solutions-verified/    complexity proved, not just tested  10
    solutions-nlogn/       the two sort rows at the tight bound 2

Only rows from `solutions/` were moved. A quarantined row stays quarantined and
carries `safety_verified` in `dataset.jsonl` instead — its label problem is the
more serious one.

## Honest note

`1944_50` is one of the five translations I hand-wrote in step 5 to prove the
pipeline end-to-end. It fails verification on a postcondition. Being written
carefully by hand and passing 101 tests was not enough to make it provably safe.
