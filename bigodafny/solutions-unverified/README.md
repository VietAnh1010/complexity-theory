# `solutions-unverified/`: tests pass, `dafny verify` does not

Rows that are safe on the stored tests but unproven on other inputs. `dafny verify`
cannot prove the checks Dafny adds by itself (indexes in range, no division by
zero, recursion that ends).

| Row | What the verifier rejects |
|---|---|
| `1336/1336_157.dfy` | a function precondition at line 58 |
| `1369/1369_10.dfy` | a `decreases` expression might not decrease |
| `1369/1369_14.dfy` | a `decreases` expression might not decrease |

## Getting a row out

Full procedure: `.claude/skills/bigodafny-verify/SKILL.md`.

1. Add the weakest `requires` that lets the check pass.
2. Run `precheck.py`: the `requires` must accept every input the row's tests
   use.
3. Re-run `dafny verify` on the row (`verify_all.py`) and `validate.py`.
4. `git mv` the row into `solutions/`.

Never add an `assume` or a `decreases *`.
