# Resuming this run

Stopped deliberately to preserve quota, not because anything broke.

## Do this first

```bash
cd bigodafny
touch experiments/runs/pilot1/AGENTS_CONFINED     # RE-ARM the guard
python3 experiments/waves.py --run-id pilot1 --todo
```

**The guard is currently disarmed** (`AGENTS_CONFINED.disarmed`). While it is
off, a blind agent can read the label straight out of `solutions/`, and any
example run in that state is contaminated and must be discarded. It was
disarmed because while armed it blocks *every* subagent in the session from the
repository, which would break unrelated work.

## Where the run stopped

Session quota, mid re-run of `1047_641`. Both v4 agents died before doing any
work and left bare stubs (`notes: "Not started yet."` on labeled, a guess and
nothing else on blind). `task.dfy` is pristine in both arms.

- 43 rows graded. `results.csv` and `RESULTS.md` are current.
- Paired plan: `794_794`, `1180_626`, `1039_15` done. **`1047_641` needs a
  clean re-run under v4** -- delete both stub `result.json`s first. Then
  `3029_114` remains.
- **Four runs are invalidated by apparatus error**, archived under
  `invalidated_v2v3/` and listed in `guide_v2_sids.json`: `1180_626` and
  `1047_641`, both arms, all of which declined on a `Join` charge that guides
  v2 and v3 wrongly forbade. Re-run before the decline rate is quoted.

## Pass the prompt INLINE, never a path to it

`harvest.py` identifies an experiment transcript by finding `cx-run/<run-id>/`
and `result.json` **in the launch prompt**. Launching an agent with "read this
file and follow it" puts neither string there, so the whole trajectory is
skipped: no tool counts, no dafny calls, no leak audit, and the example looks
un-run even after the agent finishes. Paste the output of `prompts.py` into the
agent call.

This also keeps the arms symmetric. An agent told to fetch its own instructions
spends a call doing it and reads them in a different frame from one handed them
directly; "everything else is identical" has to include that.

## The shape that works

One example per agent, the labeled and blind agent for the SAME example
launched together as a pair. Sonnet. Prompt from:

```bash
python3 experiments/prompts.py --arm labeled --run-id pilot1 --sids 1180_626
python3 experiments/prompts.py --arm blind   --run-id pilot1 --sids 1180_626
```

After each pair:

```bash
export PATH="$PATH:/root/.dotnet/tools"
python3 experiments/grade.py     --run-id pilot1 --arm both --only <sid>
python3 experiments/harvest.py   --run-id pilot1
python3 experiments/aggregate.py --run-id pilot1
```

## Two quota facts

- Each Sonnet agent costs roughly 130-180k output tokens on one of these.
- Two windows each allowed about 4-5 agents before a 429. Batches of four
  were the wrong unit: every cutoff landed mid-batch. Pairs of one survive it.

## What must not be re-derived

`RESULTS.md` states the reading rules. The three that were arrived at the hard
way, each after producing a wrong number first:

1. A step counter proves an UPPER bound, so it refutes a label only by proving
   something strictly TIGHTER. Six of eight agent `refutes` verdicts do not
   meet that bar. The agent's verdict is its belief; `direction` is the result.
2. A `gave_up` stub with an untouched `task.dfy` is a rate-limit casualty or an
   agent still running, not a give-up. Excluded from proof rate, but a blind
   stub's `guess` is real and stays in the guess accuracy.
3. A constant bound on a program that loops over its input is degenerate --
   bought by folding the statement's numeric cap into the constant. Flagged,
   never counted as a refutation.
