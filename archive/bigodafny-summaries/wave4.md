# Wave 4 (interrupted)

All four agents were killed by the account session limit mid-flight. Rows
`1263_1960` .. `1650_428`.

| batch | produced | valid after audit |
|---|---|---|
| 1 | 20 drafts, never compiled | 13 |
| 2 | 13 of 20 | 13 |
| 3 | 20 of 20 | 20 |
| 4 | 20 of 20 | 20 |
| **total** | **73** | **65** |

8 reverted to stubs: 7 build failures, 1 wrong answer (`1560_63`, 10/12 tests).

## The finding: dying agents leave work that looks finished

Batch 1's agent wrote all 20 translations as `*.dfy.new` and died before renaming
them into place. The `.dfy` files were still stubs, so the batch read as 0/20
while 20 complete drafts sat beside them, untracked.

Promoting and validating them: **13 passed, 7 failed to compile**. The agent had
not run the validator on any of them yet.

Two things follow. Drafts recovered from a dead agent are worth promoting — 13
rows were real work. And they must never be trusted: a third of that batch would
not compile. An agent's output is a proposal until the validator says otherwise,
and an agent killed before its own validation step has proposed nothing.

## Recovery notes

- Reverting by regex on the signature broke on a multi-line `method Solve(...)`.
  `git checkout -- <file>` restores the committed stub exactly and is the right
  tool, since every stub is already in git.
- `pkill -f validate.py` matches the shell running it. Use
  `ps aux | grep '[v]alidate\.py' | awk '{print $2}' | xargs -r kill`.

## Standing after wave 4

293 of 536 strict rows valid (55%). 243 strict rows remain untranslated.
The 2 `fail` rows are the parser-blocked pair in the `unvalidatable` split,
unchanged since wave 3.
