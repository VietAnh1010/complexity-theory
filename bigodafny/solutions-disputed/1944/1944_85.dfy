// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-batch-13
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The inner while loop's S accumulates by i each pass while i grows by
//     2, so it reaches S==nn in O(sqrt(nn)) iterations rather than O(nn),
//     and since nn<=5000 is capped, the outer 'while idx<|numbers|' loop
//     dominates at O(n); the Python has the identical range(3,n+5,2) loop
//     with a break, so the label overstates both.
//
//   how this label could be wrong, and what to check:
//     The label implies the inner search scales with the value s. Check
//     that 'while i<nn+5 && S!=nn' converges in O(sqrt(nn)) steps because
//     S accumulates roughly quadratically in the loop counter i, and that
//     nn<=5000 is capped by the problem statement; if both hold, per-test
//     cost is a bounded constant and the total is O(n) in the test count,
//     not O(n^2).
//
//   structural facts (deterministic, from labelaudit.py):
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
