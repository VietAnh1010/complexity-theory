# `solutions-proved/`: complexity labels, machine-checked

One proof per row. All must verify without `assume`; `proofs.py` re-checks
them into `data/complexity_proofs.jsonl`. "Proved" is about the label;
"verified" (`dafny verify`) is about safety.

Each file is a **copy** of a row with a step counter added. The row itself
stays in its own status directory (`STATUS.md` counts proofs per directory and
per label).

So a row exists twice. Scripts that walk the corpus must check both copies
(`precheck.py`'s `find_all` does), and gates must test the row, not the copy:
the two can differ where a proof broke the rules below.

`value-bounded/` holds proofs whose bound depends on an input's value; see its
README.

## Writing a proof

Procedure: `.claude/skills/bigodafny-prove/SKILL.md`. Charges:
`COMPLEXITY.md`. Sort and binary-search lemmas are in `prelude.dfy`
(`SortCostNLogN`, `SortCostWithin`, `SearchPot`, `BisectStep`,
`SearchLoopWithin`).

A proof may add only ghost code: it must compile to the same Python as its
row, and never change a `requires` on the row's code. `audit.py` checks both,
but only for rows a campaign drew.

Some proofs charge `|s|` for a sequence update where the model charges 1:
correct, not tight.
