// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The inner oi/j double loop is O(n**2) per pass, but the enclosing
//     `while flag` repeats it until no element exceeds a divisor, which is
//     a Euclid-style mod reduction taking about O(log max a_i) passes, so
//     the cost is roughly O(n**2 log max a_i); the Python pays the same
//     repeated `while True` passes, so the label is the one that omits the
//     value term.
//
//   how this label could be wrong, and what to check:
//     The label assumes the outer `while flag` loop runs a constant number
//     of passes of the O(n**2) double loop. Check how many passes the loop
//     takes: each pass reduces the minimum like a Euclid step on the
//     values, so the pass count depends on the a_i values (up to 100), not
//     on n. If the passes are provably bounded by a constant independent
//     of values, the label stands.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 51, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString"], "loop_depth": 3,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 389_A. Fox and Number Game  (problem 281, solution 281_12)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = eval(input())
// no = list(map(eval,input().split()))
// while True:
//     flag = False
//     for i in no:
//         if i<=0:
//             continue
//         for j in range(n):
//             if no[j]>i:
//                 flag = True
//                 if no[j]%i == 0:
//                     no[j] = i
//                 else:
//                     no[j] = no[j]%i
//     if flag == False:
//         break
// # print(no)
// sum = 0
// for i in no:
//     sum += i
// print(int(sum))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  decreases *
{
  var no := a_list;
  var flag := true;
  while flag
    invariant |no| == n
    decreases *
  {
    flag := false;
    var oi := 0;
    while oi < n
      invariant 0 <= oi <= n
      invariant |no| == n
      decreases n - oi
    {
      var iv := no[oi];
      if iv > 0 {
        var j := 0;
        while j < n
          invariant 0 <= j <= n
          invariant |no| == n
          decreases n - j
        {
          if no[j] > iv {
            flag := true;
            if no[j] % iv == 0 {
              no := no[j := iv];
            } else {
              no := no[j := no[j] % iv];
            }
          }
          j := j + 1;
        }
      }
      oi := oi + 1;
    }
  }
  var total := 0;
  var k := 0;
  while k < |no|
    decreases |no| - k
  {
    total := total + no[k];
    k := k + 1;
  }
  output := IntToString(total);
}
