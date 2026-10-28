# Changelog

What changed in `fuzzing/`, newest first, one dated section per session and one bullet
per change. Earlier changes are in `git log -- bigodafny/fuzzing`. Findings go in
`experiments/fuzz/FINDINGS.md`, open work in `TODO.md`.

## 2026-10-28

- `steptrace.py --counter NAME` and `fuzz.py --counter NAME` run a `.dfy` whose counter is not
  `steps`, such as `annotate counter=NAME`'s output for a row that already declares `steps`.
  `fuzz.py --bound` adds `ensures NAME <= E`. `guard.py` does not accept `--counter`.
- `steptrace.py` has no `--log` and no `LOG_CAP`; nothing used them.
- The plugin's `trace=loops` traces loop heads only; `Deghost.TraceKinds`, the point kinds to
  insert, replaces the `Trace` flag. `fuzz.py` uses it for the loop reruns, so a call compiles
  the row twice, not 3 times.
- `fuzz.py` ends a generated input with a newline only if one of the row's stored tests ends
  with one; it added one to every input, which broke parsers like `2183_1`'s.
- `fuzz.py --time-limit S` (default 300) skips inputs and loop reruns not started within
  S seconds and counts the inputs as `time-limit`. `BRIEF.md` gives agents the cap (`{{TIME_LIMIT}}`);
  `guard.py` does not accept the flag.

## 2026-10-26

- `BRIEF.md` lists `O(n**1.5)` among the class forms, and `guard.py` accepts a `.` in a class.
  Before, the Stop hook blocked every `O(n**1.5)` and `O(n**0.5)` answer once.
- `experiments/fuzz/README.md` § Fabricated rows: how to write, measure and stage one.

## 2026-10-22

- `TODO-fuzzing.md` is `TODO.md`, as the directory already names it.
- `fuzz.py`, `guard.py` and `blind.py` are split into named helpers; `BRIEF.md` and the
  README are reworded. Behaviour is unchanged.
- `fuzz.py --bound 'E'` runs the row with `ensures steps <= E` added to `Solve`. `guard.py`
  accepts `--per` and `--bound` in any order.
- `fuzz` call k writes `attempts/<k>/table.txt`: the `.dfy`, E, the attempt holding the `gen.py`
  that ran, and the table. It copies `gen.py` there only when it changed.
- A fuzz row's `answer.json` has `skipped`; `guard.py` requires it. `grade` adds `fuzz_calls`,
  `bound_tests` and `gen_versions`, and a fuzz calls column.
- Batches are named by setup time, `YYYYMMDD-HHMM`: `runs/b10` is `runs/20261021-1804`,
  `runs/live` is `runs/20261022-1236`.
- `setup` writes one shared `prelude.dfy` per batch; `guard.py` lets Read and Grep open it.
- Run output locations go in `experiments/fuzz/FINDINGS.local.md` (git-ignored).
- `fuzz` is a script again: `fuzz_mcp.py` is `fuzz.py DFY GEN [--per N]`, which prints the table.
  `blind-guess.md` starts no MCP server, so concurrent agents share nothing.
- `blind-guess` has Bash. `guard.py` allows one command, `CMD DFY GEN [--per N]`, where `CMD`
  is the venv's Python and the path of `fuzz.py`. Both files must be in the agent's own row,
  and the call must not run in the background. Bash is denied in `code` mode.
- `setup` writes `CMD` into `BRIEF.md` (`{{FUZZ}}`). `BRIEF.md` gives the command and a Bash
  timeout of 600 s.
- `steptrace.build` names a file's build directory by the file's name too, so `row.dfy` and
  `round-k.dfy` of one row can build at the same time.

## 2026-10-21

- The blind experiment only guesses the class; the prove brief, `GUESS.md` and `CLOUD.md`
  are gone. Modes `code` and `fuzz`.
- `blind.py setup|grade` replaces `stage.py` and `grade.py`; paths are explicit
  (`--dir`, `--out`).
- `BRIEF.md` is one template with a block per mode, and ends with the problem statement;
  `statement.txt` is gone.
- `setup` hands its `--dir` to `guard.py` through `experiments/fuzz/guard-path` (git-ignored).
- The agent `blind-fuzz` is renamed `blind-guess`.
- `fuzz` is an MCP tool (`fuzz_mcp.py`) that `blind-guess.md` starts; it replaces the
  generated `./fuzz` script and `run.py`. The agent has no Bash.
- `fuzz` no longer runs the stored tests or writes `run-<file>/`; `gen.py` runs in a
  child process.
- `guard.py` allows only listed tools, each with its path arguments, including
  `SubagentHandback`.
- `gen.py` is trusted: `BRIEF.md` says it only builds input text, and `grade` no longer
  scans it.
- An input `data/constraints.jsonl` rejects is counted `out-of-spec`, not `limits`.
- `answer.json` has `example`; `worst_case` and `reasoning` use the code's variables and loops.
- `grade` shows `-` for a missing answer, and the `(void)` legend only when a row is void.
- `stepfuzz.py`, `docs/08-stepfuzz.md` and the `./trace` wrapper are deleted; docs 09 and 10
  are now 08 and 09.
- `BRIEF.md` fixes the form of `class` to the labels' (`O(nlogn)`, `O(n**2)`, `O(n*m)`);
  `grade` adds `match`, and `✓` in its table.
- `guard.py` is also the agent's Stop hook: it blocks the stop until `answer.json` has every
  key and `class` in form; after 3 blocks it fails and logs the row void.
- `fuzz` adds a missing final newline to each input, as Python's `input()` allows it, and shows
  the first `parse` error.
- `fuzzing/AGENTS.md`: ignore rules for `fuzzing/` go in `fuzzing/.gitignore`.
