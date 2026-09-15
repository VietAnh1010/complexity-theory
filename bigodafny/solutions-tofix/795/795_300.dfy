// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The triple nested while loops over i<=nv/3, j<=nv/5, k<=nv/7 are all
//     bounded by the same per-test value nv, giving worst-case O(nv**3)
//     per test, which is cubic and outside the O(n**2) label; the Python's
//     identical triple `for` loop with the same early-break `f==1` guard
//     is equally cubic, so the label is wrong for both sources.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 53, "data_dependent_loops": 3, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 4, "loops": 4, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1430_A. Number of Apartments  (problem 795, solution 795_300)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// while(t>0):
//     n=int(input())
//     f=0
//     for i in range(n//3+1):
//         if(f==1):
//             break
//         for j in range(n//5+1):
//             if(f==1):
//                 break
//             for k in range(n//7+1):
//                 if(f==1):
//                     break
//                 if(3*i+5*j+7*k==n):
//                     print(i,j,k)
//                     f=1
//                     
//                     
//     if(f==0):
//         print(-1)
//     t=t-1
//         
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var parts: seq<string> := [];
  var t := 0;
  while t < n && t < |numbers|
    invariant 0 <= t
    decreases n - t
  {
    var nv := numbers[t];
    var found := false;
    var bi := 0;
    var bj := 0;
    var bk := 0;
    if nv >= 0 {
      var i := 0;
      while i <= nv / 3 && !found
        invariant 0 <= i
        decreases (nv / 3 + 1) - i
      {
        var j := 0;
        while j <= nv / 5 && !found
          invariant 0 <= j
          decreases (nv / 5 + 1) - j
        {
          var k := 0;
          while k <= nv / 7 && !found
            invariant 0 <= k
            decreases (nv / 7 + 1) - k
          {
            if 3 * i + 5 * j + 7 * k == nv {
              bi := i;
              bj := j;
              bk := k;
              found := true;
            }
            k := k + 1;
          }
          j := j + 1;
        }
        i := i + 1;
      }
    }
    if found {
      parts := parts + [IntToString(bi) + " " + IntToString(bj) + " " + IntToString(bk) + "\n"];
    } else {
      parts := parts + ["-1\n"];
    }
    t := t + 1;
  }
  output := Join(parts, "");
}
