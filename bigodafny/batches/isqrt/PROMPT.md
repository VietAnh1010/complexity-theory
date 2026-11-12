FIRST ACTION: call the Skill tool with skill="my-concise". Follow it for all
prose. Code is exempt.

# Task
Each row in your manifest is a Dafny translation of a Python program that takes
a square root (`math.sqrt`, `math.isqrt`, `** 0.5`). The Dafny rows compute it
in different ways today: a linear search, a binary search, a doubling search.
Make every row compute each square root the Python takes with ONE call to the
prelude's `ISqrt(x)` (floor of the square root; `ISqrt(x) == 0` for `x <= 0`),
at the same place the Python takes it. Change nothing else.

Working directory: bigodafny/ (from the repository root)
Manifest: batches/isqrt/w_{{NN}}.txt -- one row path per line. Edit each file
where it is; never move it. `dafny` and `z3` are on PATH. Python:
`.venv/bin/python3`.

Prelude facts you can use (already imported):
- `function ISqrt(x: int): nat`
- `lemma ISqrtSpec(x)` (requires `x >= 0`): `ISqrt(x)*ISqrt(x) <= x < (ISqrt(x)+1)*(ISqrt(x)+1)`
- `lemma LeISqrt(t, x)`: `t*t <= x ==> t <= ISqrt(x)`

# How to map the Python
- `math.isqrt(x)`, `int(math.sqrt(x))`, `int(x ** 0.5)`, `math.floor(math.sqrt(x))`
  -> `ISqrt(x)`.
- `math.ceil(math.sqrt(x))` -> `var r := ISqrt(x); if r * r < x { r := r + 1; }`.
- A perfect-square test (`sqrt(x) == int(sqrt(x))`, `isqrt(x)**2 == x`) ->
  `ISqrt(x) * ISqrt(x) == x` (bind `ISqrt(x)` to a variable once).
- A loop bound `range(..., int(sqrt(n)) + 1)` -> compute `ISqrt(n)` once before
  the loop, then loop to it, as the Python does.
- A square root used as a non-integer value (printed as a float, or in a
  formula that keeps the fraction): keep the row's exact-arithmetic approach,
  using `ISqrt` wherever it needs the floor of a square root.
- A loop in the Dafny that exists only to find a square root goes away.
- A loop like `while i * i <= n` that copies a Python loop (the Python itself
  loops while `i * i <= n`) is the Python's own loop: keep it.
Delete helper methods that become unused (e.g. `IntSqrt`, `CeilSqrt`).

# Gates after each row
1. `dafny verify <path> --verification-time-limit 30` -- must end
   `N verified, 0 errors` with no time-out. `ISqrtSpec` usually supplies what a
   removed loop's invariants did.
2. Strict rows: `.venv/bin/python3 validate.py --only <SID> --out-prefix sq{{NN}}_`
   Loose rows: `.venv/bin/python3 difftest.py --only <SID>` (`agrees` passes).
If a row will not pass both after ~10 tool calls, restore it with
`git checkout -- <path>` and report why.

# Rules
- **NEVER use `assume` or `decreases *`.**
- Keep the header, `include`, `import`, `Solve` signature and every `requires`.
  Add a `requires` only if the problem guarantees it.
- Do not change anything except the square-root computations and what they
  make unused.

# Hard rules
- NEVER git add/commit/push/mv. `git checkout --` on your own files is allowed.
- Edit ONLY the files in your manifest. NEVER edit prelude.dfy, any *.py,
  anything under data/, batches/, or solutions-proved/.

# Report (concise)
- per row: `changed` (what the square root was, what it is now), `no change`
  (reason), or `restored` (blocking error)
- every `requires` you added
