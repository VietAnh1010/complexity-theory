# `prove-sample/` — can a bounded agent prove a random row's label?

50 rows drawn from the 329 in `solutions/` that pass their gate, carry a
label, and have no proof in `solutions-proved/`. Seed **20260917**. Three
Sonnet agents, one slice each, **3 attempts and 5 minutes per row**.

**Result: 40 proved, 10 unresolved.** Every proved file was re-verified here
with `dafny verify`, not taken from an agent's report — one agent's prose
said 9 where its trajectory said 10, and the trajectory was right.

## The rate is not flat — it is a function of the label

| label | drawn | proved |
|---|---|---|
| `O(n)` | 24 | **24** |
| `O(n+m)` | 3 | 3 |
| `O(1)` | 5 | 4 |
| `O(n**2)` | 6 | 4 |
| `O(nlogn)` | 11 | **5** |
| `O(n*m)` | 1 | 0 |

Linear rows are essentially free: a ghost counter and one loop invariant.
`O(nlogn)` is where the budget goes, and **7 of the 10 failures are one
obstacle** — Z3 will not combine a recursion-tree bound with an additive term
in a single verification condition. The sort-cost lemmas verify standalone
every time; the surrounding method's postcondition is what times out.
`{:opaque}` plus `reveal` beat it three times out of five.

| obstacle | rows |
|---|---|
| `z3-nonlinear` | 7 |
| `structural-unbounded` | 2 |
| `budget` | 1 |

Only one row (`2065_24`) ran out of attempts with the mechanism already in
hand. More budget buys that row and probably some of the seven; it buys
nothing for the two structural ones.

## A proof cannot disagree with a label, and the agents said it did

All three agents recorded rows as `agrees_with_label: false`. Seven in total.
**None of them is a disagreement.**

Every bound in this campaign is an **upper** bound. A proved O(n²) on a row
labelled `O(nlogn)` does not contradict the label — it fails to confirm it.
Contradicting a label takes a **lower** bound, and nothing here produces one.
So `contradicts` is empty by construction, not by luck.

`label_relation.jsonl` carries the normalised reading per row, with the reason
written out. The agents' original booleans are kept in the payload as
`agent_said_agrees` so the normalisation stays auditable.

| relation | rows | |
|---|---|---|
| `confirms` | 33 | bound is within the label's class |
| `looser-slack` | 3 | the tight bound was not attempted |
| `looser-structural` | 4 | the proof exposes a cost the label omits |
| `unresolved` | 10 | |

The split inside `looser` is the point. `1421_89`, `1586_188` and `2742_0` are
slack — the agent says outright it used the loose sort scaffold. The other
four are not.

## The finding: value-versus-size is pervasive

Six rows — four proved-looser, two structurally unprovable — turn on whether a
loop bounded by an input **value** counts against the input **size**:

| row | what the proof exposed |
|---|---|
| `810_131` | binary search over the value `a*b`, not the query count |
| `1484_26` | string comparison costs per character: `\|numbers\| * MaxLen` |
| `2381_156` | `IntToString` costs the digit count, i.e. log of the value |
| `2607_90` | a loop range taken straight from input values |
| `2128_34` | an array sized by an input value; no bound in `n` exists |
| `2942_42` | a parameter whose sign is unconstrained |

That convention was already open across 12 rows in `solutions-disputed/`. A
random draw of 50 hitting it six more times says it is a property of the
corpus, not of the rows that happened to be audited first. **It is the single
decision that would most change the dataset**, and it is not ours to make.

## Files

| file | what it is |
|---|---|
| `manifest.jsonl` | the 50 rows: id, path, label, split, gate |
| `slice_{a,b,c}.jsonl` | the three agent assignments |
| `PROMPT.md` | the agent brief; self-contained, charge table inline |
| `traj_{a,b,c}.jsonl` | per-row attempts, bound, timing, failure reason |
| `label_relation.jsonl` | the normalised label relation, with reasons |

Proofs themselves are overlay copies in `../../solutions-proved/<pid>/`. The
originals in `solutions/` were not modified; that was checked, not assumed.
