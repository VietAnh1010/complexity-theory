// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-10
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each of the n queries builds ans with Repeat of lengths about
//     sqrt(2*t_i) and Join is linear in the total output, so the cost is
//     O(sum of sqrt(t_i)), a value term per test; the binary search over
//     the literal range 0..100000 is constant and Python's string
//     multiplication pays the same.
//
//   how this label could be wrong, and what to check:
//     The label counts test cases n, but each test pays for building a
//     string whose length depends on the value t_i. Check Repeat("3",
//     threesN) and Repeat("1", onesN) in the Dafny and the "3"*(x-1-2) and
//     "1"*(t-A[x-1]) in the Python: both produce a string of about
//     sqrt(2*t) characters, and Join pays for the total output length.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 42, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "Repeat"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1202_D. Print a 1337-string...  (problem 1867, solution 1867_16)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import bisect
// 
// Q=int(input())
// 
// A=[n*(n-1)//2 for n in range(10**5)]
// 
// 
// x=bisect.bisect(A,10**9)
// 
// 
// for testcases in range(Q):
//     t=int(input())
// 
//     if t==1:
//         print(1337)
//         continue
// 
//     x=bisect.bisect_left(A,t)
// 
//     ANS="1"+"3"*(x-1-2)+"1"*(t-(A[x-1]))+"337"
// 
//     print(ANS)
//     
//     
//     
//     
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
  requires n >= 0
  requires |numbers| >= n
{
  var lines: seq<string> := [];
  var qi := 0;
  while qi < n
    invariant 0 <= qi <= n
    decreases n - qi
  {
    var t := numbers[qi];
    if t == 1 {
      lines := lines + ["1337"];
    } else {
      var lo := 0;
      var hi := 100000;
      while lo < hi
        invariant 0 <= lo <= hi <= 100000
        decreases hi - lo
      {
        var mid := (lo + hi) / 2;
        if mid * (mid - 1) / 2 < t {
          lo := mid + 1;
        } else {
          hi := mid;
        }
      }
      var x := lo;
      var threes := x - 1 - 2;
      var threesN := if threes < 0 then 0 else threes;
      var aXm1 := (x - 1) * (x - 2) / 2;
      var ones := t - aXm1;
      var onesN := if ones < 0 then 0 else ones;
      var ans := "1" + Repeat("3", threesN) + Repeat("1", onesN) + "337";
      lines := lines + [ans];
    }
    qi := qi + 1;
  }
  output := Join(lines, "\n");
}
