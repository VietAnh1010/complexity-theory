# `solutions-unverified/`: tests pass, `dafny verify` does not

Rows that are safe on the stored tests but unproven on other inputs. `dafny verify`
cannot prove the checks Dafny adds by itself (indexes in range, no division by
zero, recursion that ends).

| Row | What the verifier rejects |
|---|---|
| `1336/1336_157.dfy` | a function precondition at line 58; `ProbeInsert` also uses `decreases *` |

## Getting a row out

Full procedure: `.claude/skills/bigodafny-verify/SKILL.md`.

1. Add the weakest `requires` that lets the check pass.
2. Run `precheck.py`: the `requires` must accept every input the row's tests
   use.
3. Re-run `dafny verify` on the row (`verify_all.py`) and `validate.py`.
4. `git mv` the row into `solutions/` if `data/label_audit.jsonl` gives it verdict `ok`, else
   into `solutions-unscreened/`.

Never add an `assume` or a `decreases *`.
