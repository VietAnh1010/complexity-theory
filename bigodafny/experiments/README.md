# Can an agent prove — and guess — the complexity label?

Two arms over the same 100 rows.

- **labeled** — the agent is told BigOBench's complexity label and must prove it
  with a ghost step counter, or refute it.
- **blind** — the agent is told nothing, must commit to a class in writing
  *before* proving, then prove its own guess.

Everything else is identical: same guide, same prelude, same problem statement,
same Python, same rules, same model. The label is the only variable.

## Why the label is worth attacking

BigOBench's labels are synthetic — a regression over profiling runs, not a
proof. The 12 rows this project has already proved disagree with their label
5 times, and 2 of those are outright wrong: `1138_83` and `1650_428` both carry
`O(n*m)` where the `m` names a scalar that does not vary with input size. Two of
two examined were wrong. That is a reason for suspicion, not a rate — which is
what a hundred examples is for.

## Running it

```bash
python3 experiments/select.py                      # -> manifest.json (100 rows)
python3 experiments/stage.py --run-id RUN          # -> both corpora, scrubbed
python3 experiments/harvest.py --run-id RUN --snapshot   # BEFORE each wave
touch experiments/runs/RUN/AGENTS_CONFINED         # arm the containment hook
python3 experiments/prompts.py --arm blind --run-id RUN --sids A B C D
#   ... spawn 4 agents at a time, sonnet, 4 examples each ...
python3 experiments/harvest.py --run-id RUN        # trajectories + leak audit
python3 experiments/grade.py   --run-id RUN
python3 experiments/aggregate.py --run-id RUN      # -> results.csv, RESULTS.md
```

`selftest_grade.py` must pass before any of it is believed.

## Selection

Pool is the 506 rows in `solutions/` — behaviourally validated *and* `dafny
verify` clean, so an agent spends its budget on complexity rather than on index
obligations. Minus the 12 already proved, whose answer is in the repo. One row
per problem, because siblings are near-duplicates: 254 candidates.

Interestingness is scored from structure — loop nesting, sorts, data-dependent
guards, recursive helpers, `set`/`map` use, multiple size arguments — plus label
rarity, so that all 11 classes survive into the sample. Five classes have five
or fewer members in the pool and are taken whole.

`difficulty_static` (1–5) is computed from the **label-free** features only and
written down before any agent runs, so comparing it against measured difficulty
afterwards is not circular.

## Stopping the blind arm from cheating

The label is not hidden in this repository. All 506 files in `solutions/` carry
`// time complexity: O(...)` in the header; `data/`, `stats.json`,
`COMPLEXITY.md`, `summaries/`, the skills and `git log` all carry it too. One
`grep` would end the experiment.

Three layers, all measured rather than asserted:

**Scrub.** The blind corpus drops the header label, the Codeforces title, and
the curve coefficient. `stage.py --check` then greps every staged blind file for
the label, the title, and any complexity-shaped token. It rests on one
invariant — *a file byte-identical across every example cannot carry a
per-example answer* — which `constancy_check` asserts rather than assumes, so
`GUIDE.md` and `prelude.dfy` can be exempted honestly.

It found one real leak on the way in: `1332_16`'s own Python carries the comment
`#Ai += x O(logN)`. Redacted from **both** arms, so the arms still differ only in
the label, and recorded in `staged.json`.

**Confine.** `guard.py` is a `PreToolUse` hook. While
`runs/<id>/AGENTS_CONFINED` exists, any subagent tool call reaching the
solutions tree, the dataset files, the project notes, the skills or git history
is denied and logged. Verified live: a probe agent asked to `cat` a solutions
file, grep the dataset for `time_complexity`, and run `git log` was denied on
all three and allowed on both reads inside its own directory.

Two things about the hook were wrong on the first attempt and are worth keeping
written down:

- it *is* loaded from project settings mid-session; no restart needed;
- a subagent's payload is identified by `agent_id`/`agent_type`, **not** by
  `transcript_path`, which names the parent session transcript in both cases.
  Reading it the other way let a probe agent walk straight into the repo while
  the hook reported success.

Both arms are confined, not just the blind one — confining only the blind arm
would make containment itself a difference between the arms.

**Audit.** `harvest.py` reads each agent's own transcript, not its report, and
flags any tool call naming a banned path. Attempts are reported, and an example
whose agent attempted one is excluded from the headline accuracy. An attempt is
a result in its own right, whether or not the guard stopped it.

## Grading: five gates, recorded separately

| gate | question |
|---|---|
| `verify` | `verifier finished with N verified, 0 errors`, and no timed-out lemma |
| `no_assume` | zero `assume`, including `assume {:axiom}` |
| `skeleton` | the **compiled** control flow is unchanged |
| `behaviour` | the row's own gate still passes (`validate` / `difftest`) |
| `bound_class` | which of the 11 classes the proved bound actually belongs to |

`skeleton` is the one that matters most, and it is the least obvious. An agent
can make any bound true by changing the algorithm — swap a quadratic scan for a
closed form and every test still passes, because the answers are identical.
Behaviour tests are blind to it. Dafny erases `ghost` material, so a real proof
leaves the emitted Python's loops untouched; an algorithm swap does not.

`selftest_grade.py` demonstrates exactly this. Its third case replaces two
accumulation loops with an uncharged recursive helper: the file verifies clean,
passes 12/12 tests, and claims constant time for a linear program. Only the
skeleton gate sees it.

## Classifying a bound

`bound.py` does not parse the expression. It substitutes sizes and keeps the
candidate class whose ratio to the expression stays bounded as the sizes grow.
Constants are arbitrary by design, expressions nest freely, and proofs charge
terms the label never names — a grammar would not survive any of that.

It deliberately does not decide which argument of `Solve` is the label's `n`.
That mapping is not declared anywhere in BigOBench, and assuming one is how two
labels here came to be wrong. It tries every assignment, reports the shape, and
returns `unclassified` rather than rounding.

Calibration on the 12 finished proofs: 7 agree with the label, and all 5
disagreements are already-known — the two disproved `O(n*m)` labels, and the two
deliberately weak quadratic fallbacks kept alongside their tight `n log n`
versions, plus one proof that charges a string-length term the label ignores.

## Known limits

- 100 of 254 eligible problems, stratified by a score that favours nested loops
  and sorts. Not a uniform sample, and not to be reported as one.
- Sonnet, four examples per agent. A low proof rate measures the model and the
  harness together, not the intrinsic difficulty of the row.
- The blind arm sees a Dafny translation that is already structured, already
  terminating, already carries `decreases` clauses. This measures inference from
  *translated* code, not from raw Python.
- `GUIDE.md` gives the blind arm the closed vocabulary of 11 classes, which
  turns an open question into an 11-way classification. It makes accuracy
  well-defined and makes the task easier; both are true.
