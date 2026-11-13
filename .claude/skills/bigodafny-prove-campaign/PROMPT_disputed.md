
## Your rows are disputed — this section overrides the label-first parts above

Every row in your slice lives in `solutions-disputed/<pid>/<sid>.dfy`, not in
`solutions/`. Read `solutions-disputed/` wherever this brief says `solutions/`;
it is the original you never modify. Your copy still goes to
`solutions-proved/<pid>/<sid>.dfy`.

A label audit doubts each row's label. The row's header comment
(`LABEL AUDIT -- queued for manual review`) gives the audit's guess
(`audited class`) and its reasoning. The label and the guess are both hints,
and either may be wrong.

Your goal is the **tightest upper bound you can prove** within the budget, not
the label:

1. Read the Python and the Dafny and decide the real cost yourself.
2. Prove that bound. If it is below the label, record `tighter-label` only after
   checking that the Python itself does no more work (see above); otherwise name
   the translation or charge-table cause.
3. If the tight bound will not close, a looser proved bound is still a result:
   record it with `looser-slack` and say in `relation_reason` what the tight
   bound would need.

`relation` is still measured against the row's label, from the same vocabulary.
