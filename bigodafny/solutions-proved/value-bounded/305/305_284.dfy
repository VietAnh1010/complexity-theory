// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
// 350_A. TL  (problem 305, solution 305_284)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// string = input()
// numbers = string.split()
// a = int(numbers[0])
// b = int(numbers[1])
// string = input()
// right = list(map(int, string.split()))
// string = input()
// wrong = list(map(int, string.split()))
// p = max(right)
// q = min(wrong)
// r = min(right)
// for x in range(p, q):
//     if r * 2 <= x:
//         print(x)
//         break
// else:
//     print(-1)
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

// MaxSeq/MinSeq are pure recursive prelude functions -- each charged its
// argument's length (COMPLEXITY.md: recursive prelude function over a seq).
// The search loop steps x from p toward q: at most q - p iterations, a
// difference of input VALUES (max(right) and min(wrong)), not a size.
method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |c_list| > 0
  requires |d_list| > 0
  ensures steps <= 2 * |c_list| + |d_list| + 3 * (if MinSeq(d_list) > MaxSeq(c_list) then MinSeq(d_list) - MaxSeq(c_list) else 0) + 6
{
  var p := MaxSeq(c_list);
  var q := MinSeq(d_list);
  var r := MinSeq(c_list);
  steps := |c_list| + |d_list| + |c_list| + 1;
  ghost var base := steps;
  // for x in range(p, q): if r * 2 <= x: print(x); break  else: print(-1)
  output := "-1";
  var x := p;
  var found := false;
  steps := steps + 3;
  while x < q && !found
    invariant p <= x
    invariant x <= q || x == p
    invariant steps <= base + 3 + 3 * (x - p) + (if found then 2 else 0)
    decreases q - x, if found then 0 else 1
  {
    if r * 2 <= x {
      output := IntToString(x);
      found := true;
      steps := steps + 2;
    } else {
      x := x + 1;
      steps := steps + 3;
    }
  }
  assert x - p <= (if q > p then q - p else 0);
}
