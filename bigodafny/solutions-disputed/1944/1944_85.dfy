// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Per test case the inner loop adds successive odd numbers to S until
//     S == nn, taking about sqrt(nn) iterations, so the total is O(sum of
//     sqrt(s_i)) plus an O(t) Join. The Python's for i in range(3, n+5, 2)
//     with the same S == n break pays the same sqrt term, so the label is
//     wrong, not the translation.
//
//   how this label could be wrong, and what to check:
//     The label treats n as a size, but n counts test cases (t <= 5000)
//     and each test pays in its value s. Check the inner while i < nn + 5
//     && S != nn loop: S adds odd numbers 3, 5, 7, ..., so it exits after
//     about sqrt(s) steps.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 40, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString", "Join"], "loop_depth":
//     2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1550_A. Find The Array  (problem 1944, solution 1944_85)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for _ in range(int(input())):
//     n=int(input())
//     if n==1: print(1);continue
//     if n==2: print(2);continue
//     if n==3: print(2);continue
//     S=1
//     c=1
//     for i in range(3,n+5,2):
//         if S==n:
//             break
//         if i+S<=n:
//             S=S+i
//             c+=1
//         else:
//             #print('enter')
//             S=n
//             c+=1
//         #print("S",S)
//     print(c)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
  decreases *
{
  var results: seq<string> := [];
  var idx := 0;
  while idx < |numbers|
    decreases |numbers| - idx
  {
    var nn := numbers[idx];
    var c: int;
    if nn == 1 {
      c := 1;
    } else if nn == 2 {
      c := 2;
    } else if nn == 3 {
      c := 2;
    } else {
      var S := 1;
      var cc := 1;
      var i := 3;
      while i < nn + 5 && S != nn
        decreases *
      {
        if i + S <= nn {
          S := S + i;
        } else {
          S := nn;
        }
        cc := cc + 1;
        i := i + 2;
      }
      c := cc;
    }
    results := results + [IntToString(c)];
    idx := idx + 1;
  }
  output := Join(results, "\n");
}
