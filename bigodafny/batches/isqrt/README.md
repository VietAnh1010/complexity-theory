# isqrt (2026-11-12)

Every row whose Python takes a square root (`math.sqrt`, `math.isqrt`, `** 0.5`; 20 rows by a
search of `solution_code`) now computes it with one call to the prelude's `ISqrt` per root the
Python takes, charged `ISqrtSteps` (`COMPLEXITY.md`). Before, the rows used a linear search, a
binary search or a doubling search, so the same Python operation had different costs. Two slices
(`w_00.txt`, `w_01.txt`), one general-purpose agent each, brief `PROMPT.md`.

## Audit (parent, from scratch)

Every changed row: `dafny verify` ends `N verified, 0 errors`; no `assume` or `decreases *` in
code; `validate.py --only` passes (all 16 are strict). No row-defined square-root helper is left
in any status directory.

## Results

- Changed (16): `5_25`, `167_177`, `342_86`, `482_366`, `704_351`, `810_131`, `1011_177`,
  `1234_71`, `1276_39`, `1276_62`, `1944_50`, `1948_388`, `2065_128`, `2358_103`, `2358_421`,
  `2819_926`.
- `482_366` also used an O(n²) double loop where the Python loops once; it now follows the Python.
- No square root taken (4): `1855_50` (only in an uncalled function), `1867_45` (imported, never
  called), `2226_607` (none), `2516_236` (only in commented-out Python).
- `342_86`, `704_351`, `810_131`, `1944_50`, `1948_388`, `2358_103`, `2358_421`, `2819_926` have
  proofs of the old code; `proofs.py` flags them until they are re-proved.
