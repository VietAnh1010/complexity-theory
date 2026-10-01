// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(logn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop in Solve visits every (l, pos) pair with l up to the bit
//     length of b and pos from l-2 down to 0, so it runs Theta((log b)**2)
//     iterations, a cost in the input value b. The Python's while True
//     loop has the identical double walk, so the O(logn) label is wrong
//     for both; true class is O((log b)**2).
//
//   how this label could be wrong, and what to check:
//     The label assumes one logarithmic pass. Read the loop: for each bit
//     length l (2 up to about log2 b) pos walks from l-2 down to 0, so the
//     iteration count is about (log2 b)**2 / 2, not log b. Confirm in the
//     Python that `l += 1; pos = l-2` restarts pos at every l.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 47, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 611_B. New Year and Old Property  (problem 1364, solution 1364_161)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// ans = 0
// a, b = map(int, input().split())
// l = 2
// pos = l-2
// ans = 0
// while True:
//     n = ((1 << l) - 1) - (1 << pos)
//     #print(l, pos, n)
//     if n > b:
//         break
//     if n >= a:
//         ans += 1
//     if pos > 0:
//         pos -= 1
//     else:
//         l += 1
//         pos = l-2
// print(ans)
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Pow2(e: nat): int
  ensures Pow2(e) >= 1
  decreases e
{
  if e == 0 then 1 else 2 * Pow2(e - 1)
}

method Solve(a: int, b: int) returns (output: string)
{
  var l := 2;
  var pos := 0; // l - 2
  var powL := 4; // 2^l
  var powPos := 1; // 2^pos
  var ans := 0;
  var done := false;
  while !done
    invariant l >= 2
    invariant 0 <= pos <= l - 2
    invariant powL == Pow2(l)
    invariant powPos == Pow2(pos)
    invariant powPos >= 1
    invariant powL >= 4
    decreases (if done then 0 else 1), (if powL - 1 - powPos > b then 0 else b - (powL - 1 - powPos) + 1)
  {
    var n := powL - 1 - powPos;
    if n > b {
      done := true;
    } else {
      if n >= a {
        ans := ans + 1;
      }
      if pos > 0 {
        assert powPos == Pow2(pos) && pos - 1 >= 0;
        assert Pow2(pos) == 2 * Pow2(pos - 1);
        pos := pos - 1;
        powPos := powPos / 2;
      } else {
        l := l + 1;
        pos := l - 2;
        powPos := powL / 2;
        powL := powL * 2;
      }
    }
  }
  output := IntToString(ans);
}
