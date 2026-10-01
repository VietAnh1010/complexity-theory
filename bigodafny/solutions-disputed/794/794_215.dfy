// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the test list once; per test the `while i < nv`
//     divisor search and the three append loops (cnt = nv) plus JoinInts
//     cost O(nv), so tests times per-test array length is O(n*m), not
//     O(n**2); the cap n <= 50 is a statement cap. The Python has the same
//     range(1,n) loop and while n>0 loops, so the label is wrong.
//
//   how this label could be wrong, and what to check:
//     The label assumes quadratic work in one size. Check the per-test
//     loops: `while i < nv` runs to the per-test array length nv and the
//     three append loops (cnt = nv) plus JoinInts are also O(nv), while
//     the test count loops only once.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 55, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "JoinInts"], "loop_depth":
//     2, "loops": 5, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1409_C. Yet Another Array Restoration  (problem 794, solution 794_215)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for _ in range(t):
//     n,x,y=list(map(int,input().split()))
//     d=y-x
//     for i in range(1,n):
//         if (y-x)%i==0:
//             d=min(d,(y-x)//i)
//     ans=[]
//     p=x
//     while p<=y and n>0:
//         ans.append(p)
//         p=p+d
//         n=n-1
//         if p>y:
//             break
//     p=x-d
//     while p>0 and n>0:
//         ans.append(p)
//         p=p-d
//         n=n-1
//     p=y+d
//     while n>0:
//         ans.append(p)
//         p=p+d
//         n=n-1
//     print(*ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, data: seq<(int, int, int)>) returns (output: string)
{
  var parts: seq<string> := [];
  var ti := 0;
  while ti < n && ti < |data|
    invariant 0 <= ti
    decreases n - ti
  {
    var (nv, x, y) := data[ti];
    var diff := y - x;
    var d := diff;
    var i := 1;
    while i < nv
      invariant 1 <= i
      decreases nv - i
    {
      if diff % i == 0 {
        var cand := diff / i;
        if cand < d { d := cand; }
      }
      i := i + 1;
    }
    var ans: seq<int> := [];
    var p := x;
    var cnt := nv;
    while p <= y && cnt > 0
      decreases cnt
    {
      ans := ans + [p];
      p := p + d;
      cnt := cnt - 1;
    }
    p := x - d;
    while p > 0 && cnt > 0
      decreases cnt
    {
      ans := ans + [p];
      p := p - d;
      cnt := cnt - 1;
    }
    p := y + d;
    while cnt > 0
      decreases cnt
    {
      ans := ans + [p];
      p := p + d;
      cnt := cnt - 1;
    }
    parts := parts + [JoinInts(ans, " ") + "\n"];
    ti := ti + 1;
  }
  output := Join(parts, "");
}
