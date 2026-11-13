# verify-clean (2026-11-12)

Stage B of the clean-636 plan: every row that failed `verify_all.py`'s first full sweep, or
verified only with `decreases *`. 96 rows in five slices (§ Rows), one general-purpose agent per slice, brief `PROMPT.md`. Agents edited rows in place; nothing
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

## Rows

- `w_00`: `64_1063`, `225_145`, `225_85`, `229_3630`, `281_12`, `281_138`, `281_250`, `294_56`, `310_121`, `333_197`, `333_21`, `333_536`, `397_163`, `397_80`, `408_1572`, `408_2`, `457_38`, `522_46`, `522_62`, `565_118`
- `w_01`: `565_158`, `619_340`, `619_362`, `700_233`, `700_99`, `716_174`, `716_514`, `772_19`, `772_6`, `788_22`, `804_42`, `914_14`, `914_416`, `960_63`, `1017_834`, `1017_937`, `1039_146`, `1092_0`, `1092_11`
- `w_02`: `1231_51`, `1231_541`, `1234_634`, `1234_71`, `1310_1170`, `1310_3062`, `1336_157`, `1357_135`, `1369_10`, `1369_14`, `1413_104`, `1413_222`, `1548_179`, `1548_552`, `1577_173`, `1577_411`, `1577_61`, `1628_26`, `1628_32`
- `w_03`: `1640_35`, `1640_36`, `1671_196`, `1671_68`, `1675_29`, `1722_4`, `1741_12`, `1742_66`, `1742_78`, `1853_137`, `1853_66`, `1870_58`, `1870_81`, `1871_291`, `1913_104`, `1913_99`, `1944_85`, `1948_38`, `1948_388`
- `w_04`: `1972_295`, `1997_199`, `1997_311`, `2007_136`, `2185_148`, `2325_570`, `2325_862`, `2381_176`, `2482_13`, `2577_283`, `2577_822`, `2680_65`, `2704_62`, `2704_92`, `2773_68`, `2847_21`, `2847_36`, `2854_107`, `2854_30`
