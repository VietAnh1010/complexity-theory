// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops t over |matrix| and each row is read at three fixed
//     indices; the nested `while i/j/k <= 1` loops have literal bounds, so
//     the cost is O(n) in the test count and row width never enters; the
//     Python's l=list(map(int,...)) is a fixed 3-element row too.
//
//   how this label could be wrong, and what to check:
//     The label assumes a second dimension m. Check the input: each test
//     row is exactly three integers a, b, c, and Solve reads row[0],
//     row[1], row[2] only; the 27-point neighbourhood loops are fixed
//     literals.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 45, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 4, "loops": 4, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1272_A. Three Friends  (problem 1134, solution 1134_120)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def dis(a,b,c):
// 	return abs(a-b)+abs(b-c)+abs(a-c);
// t=int(input());
// while(t>0):
// 	t-=1;
// 	l=list(map(int,input().split()));
// 	a=l[0];
// 	b=l[1];
// 	c=l[2];
// 	ans=dis(a,b,c);
// 	for i in range(-1,2):
// 		for j in range(-1,2):
// 			for k in range(-1,2):
// 				x=a+i;
// 				y=b+j;
// 				z=c+k;
// 				s=dis(x,y,z);
// 				if(s<ans):
// 					ans=s;
// 	print(ans);
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| >= 3
{
  var lines: seq<string> := [];
  var t := 0;
  while t < |matrix|
    invariant 0 <= t <= |matrix|
    decreases |matrix| - t
  {
    var row := matrix[t];
    var a := row[0];
    var b := row[1];
    var c := row[2];
    var ans := Dis(a, b, c);
    var i := -1;
    while i <= 1
      decreases 1 - i
    {
      var j := -1;
      while j <= 1
        decreases 1 - j
      {
        var k := -1;
        while k <= 1
          decreases 1 - k
        {
          var s := Dis(a + i, b + j, c + k);
          if s < ans { ans := s; }
          k := k + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    lines := lines + [IntToString(ans)];
    t := t + 1;
  }
  output := Join(lines, "\n");
}


function Dis(a: int, b: int, c: int): int
{
  AbsInt(a - b) + AbsInt(b - c) + AbsInt(a - c)
}
