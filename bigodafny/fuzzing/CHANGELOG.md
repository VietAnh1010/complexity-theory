# Changelog

What changed in `fuzzing/`, newest first, one dated section per session and one bullet
per change. Earlier changes are in `git log -- bigodafny/fuzzing`. Findings go in
`experiments/fuzz/FINDINGS.md`, open work in `TODO-fuzzing.md`.

## 2026-10-22

- A `fuzz` row's `answer.json` has `skipped`: each step the agent chose not to take, and why;
  `guard.py` requires it there. `grade` adds `fuzz_calls`, `bound_tests` and `gen_versions` from `attempts/`, and
  a fuzz calls column to the run table.
- `fuzz.py` call k writes `attempts/<k>/table.txt` in the row directory: the `.dfy` it ran, the
  attempt whose `gen.py` it ran, then its table. It copies `gen.py` there only when changed. A
  `round-k.dfy` goes in the table as a diff from `row.dfy` and is deleted. `grade` copies
  `attempts/` with the row.
- A batch is named by its setup time, `YYYYMMDD-HHMM` (`/tmp/fuzz-blind/20261022-1258`,
  `runs/20261022-1258`). `runs/b10` is `runs/20261021-1804`; `runs/live` is `runs/20261022-1236`.
- `setup` writes one `prelude.dfy` in `--dir`; each `row.dfy` includes `../../prelude.dfy`.
  `guard.py` lets Read and Grep open it, and `BRIEF.md` gives its path (`{{PRELUDE}}`).
- Where run outputs lie goes in `experiments/fuzz/FINDINGS.local.md` (git-ignored), not in
  `FINDINGS.md`.
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
