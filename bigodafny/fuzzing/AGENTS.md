# fuzzing/ rules

- Put every ignore rule for a path under `fuzzing/` in `fuzzing/.gitignore`, not in
  `bigodafny/.gitignore` or the repository's.
- Record each change to `fuzzing/` as a bullet under today's date in `fuzzing/CHANGELOG.md`;
  findings of experiment runs go in `experiments/fuzz/FINDINGS.md`.
