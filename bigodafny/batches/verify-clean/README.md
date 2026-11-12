# verify-clean (2026-11-12)

Stage B of the clean-636 plan: every row that failed `verify_all.py`'s first full sweep, or
verified only with `decreases *`. 96 rows in five slices (`w_00.txt` to `w_04.txt`, one row path per
line), one general-purpose agent per slice, brief `PROMPT.md`. Agents edited rows in place; nothing
moved.

## Audit (parent, from scratch)

- `dafny verify` on every row; a pass needs `N verified, 0 errors` and no time-out.
- Comment-stripped grep for `decreases *` and `assume`.
- `precheck.py` on every row of a slice. Three clauses failed only on generated tests outside the
  statement's limits; those limits are now quoted in `data/constraints.jsonl` (problems 565, 772).
- `validate.py --only` (strict) and `difftest.py --only` (loose) on every changed row.

## Results

| Slice | Rows | Verify, no `decreases *` | Unchanged |
|---|---:|---:|---|
| w_00 | 20 | 20 | |
| w_01 | 19 | 19 | |
| w_02 | 19 | 18 | `1336_157`: `ProbeInsert` simulates CPython set probing; termination needs a proof that probing visits every slot |
| w_03 | 19 | 19 | |
| w_04 | 19 | 19 | |

Every added `requires` holds on every counted stored input. `772_19` and `772_6` initialise
`new int[2*size]` explicitly to 0 (`(_ => 0)`), the value Dafny already gives; the verifier needs
it for the `bv64` reads.

## Translations that swap the Python's algorithm

Agents reported these; none was changed here. They break `CLAUDE.md` § Keep the algorithm and go to
re-translation:

- `1671_196`: merge sort where the Python does insertion sort.
- `1742_66`: linear scan where the Python sorts.
- `1853_137`, `1853_66`: an O(n²) pair loop where the Python sorts or counts.
- `565_158`: counting array where the Python sorts.
- `700_233`, `700_99`: closed form where the Python loops k times.
- `1997_311`: drops the Python's sort.

`2007_136` was also reported: when both neighbours in `l[i-1]` equal `j`, the Python appends
nothing and the Dafny appends one. The problem's input never has that shape, and on it the Python
never finishes, so this is not a defect.
