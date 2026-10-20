# Findings

What the blind runs of 2026-10-20 showed. Run outputs are in `fuzzing/demo/blind/`
(git-ignored, local only).

## Loose proofs come from settling, not from wrong guesses

Five proofs in `solutions-proved/` were a class looser than their code. Their agents
were shown the label and asked to prove it. None guessed the class wrong; each
proved an easier goal:

| Row | Label | Old proof | Tight | Why the old proof was loose |
|---|---|---|---|---|
| `2586_20` | O(n**2) | O(n**3) | O(n**2) | bounded each inner scan by the whole array (n**2) instead of the slots already filled (at most i); the agent named the amortized argument and recorded `looser-slack` |
| `1820_180` | O(n) | O(n**2) | O(n), as x, y <= 7 | bounded each window by the list length instead of x + y; recorded `looser-structural` |
| `2913_484` | O(n) | O(n) | O(sqrt n) | the agent wrote that the loop runs about sqrt(x) times, then proved 4n + 6 because it matched the label |
| `5_100`, `1011_368` | O(n) | O(n) | O(sqrt n) | no campaign record |

A proof only has to hold, and the old workflow counted any verified bound as a
success. Nothing checked tightness, so an agent could settle for a bound that is
easier to prove: a per-iteration worst case times the iteration count, or the label.

Two things counter it:

- **Ask blind for the tightest class before proving.** Blind agents named the tight
  class from the code on all five rows, and proved it on three. Two hit the
  3-attempt budget: `5_100` on a square-root lemma (now `ISqrt` in the prelude) and
  `2586_20` on counting the filled slots; both tight proofs were finished by hand.
- **Measure steps against the proved bound.** Running every proof on its stored tests
  and fitting log(steps) against log(bound) found all five
  (`docs/07-steptrace.md` § Screening proofs for loose bounds).

## Running inputs did not improve guessing

Twelve hard rows (amortized loops, sorts inside loops, helper chains), each guessed
by two blind Sonnet agents: one from the code only, one with `./fuzz`. Both named the
reference class on all twelve. The code-only agents took 14-31 s a row; the runs
added 30 s to 4 min and changed no answer. Earlier, eleven guess-measure-prove rows
never changed class after measuring either.

Runs are weak evidence when sizes are small: on `2072_40` (n <= 100) the measured
steps looked linear and the true class is O(n log n).

## Where runs help

- Finding loose proofs, above.
- Catching a bound that is too low before a proof attempt (`1699_213`'s first bound
  broke at n = 1).
- Evidence against a label that is too low: a family of inputs whose steps outgrow the
  label. An upper-bound proof cannot show this.
