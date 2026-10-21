# Changelog

What changed in `fuzzing/`, newest first, one dated section per session and one bullet
per change. Earlier changes are in `git log -- bigodafny/fuzzing`. Findings go in
`experiments/fuzz/FINDINGS.md`, open work in `TODO-fuzzing.md`.

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
- `fuzzing/AGENTS.md`: ignore rules for `fuzzing/` go in `fuzzing/.gitignore`.
