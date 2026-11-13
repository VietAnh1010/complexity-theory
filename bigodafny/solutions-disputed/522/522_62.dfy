// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Python builds four complex numbers from `P[i*2]`, `P[i*2+1]` for
//     i in range(4) and the Dafny reads `pts[0]` to `pts[7]`, a fixed
//     eight values per row over n rows, so the cost is O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes the row width varies. Each dataset is exactly
//     eight coordinates and both programs read a fixed four points from
//     it. Check the input format: eight reals per line makes m a constant
//     and the class O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 25, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     1, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// p00021 Parallelism  (problem 522, solution 522_62)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N = int(input())
// for _ in range(N):
//     P = list(map(float,input().split()))
//     a, b, c, d = [complex(P[i*2],P[i*2+1])*1000000 for i in range(4)] 
//     parallel = ((a-b).conjugate() *(c-d)).imag ==0
//     print("YES" if parallel else "NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, points_list: seq<seq<real>>) returns (output: string)
  requires n <= |points_list|
  requires forall k :: 0 <= k < |points_list| ==> |points_list[k]| >= 8
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i
    decreases n - i
  {
    var pts := points_list[i];
    var x1 := pts[0]; var y1 := pts[1]; var x2 := pts[2]; var y2 := pts[3];
    var x3 := pts[4]; var y3 := pts[5]; var x4 := pts[6]; var y4 := pts[7];
    var cross := (x2 - x1) * (y4 - y3) - (x4 - x3) * (y2 - y1);
    if cross == 0.0 {
      lines := lines + ["YES"];
    } else {
      lines := lines + ["NO"];
    }
    i := i + 1;
  }
  output := Join(lines, "\n") + "\n";
}
