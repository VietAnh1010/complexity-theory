// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(1)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops a literal `while i < 5` calling IndexOf1From3499 on each
//     row of a fixed 5x5 matrix; there is no sort anywhere in the Dafny or
//     the live Python (the x.sort() is commented out). The cost is
//     constant, so O(nlogn) names a growth rate no construct exhibits.
//
//   how this label could be wrong, and what to check:
//     The label claims an n log n growth rate but nothing here sorts.
//     Check that the Python only has `range(5)` with
//     `input().split().index("1")` (the sort lines are commented out) and
//     that the description fixes a 5x5 grid.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 32, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 263_A. Beautiful Matrix  (problem 531, solution 531_3499)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # n=int(input())
// # x=list(map(int,input().split()))
// # x.sort()
// # print(x)
// 
// # fi=fj=0
// # for i in range(5):
// # 		x=input().split()
// # 		k=0
// # 		for j in x:
// # 			if j=="1":
// # 				fi=i
// # 				fj=k
// # 			k+=1
// 
// # t1,t2=abs(fi-2),abs(fj-2)
// # print(t1+t2)
// 
// 
// 
// for i in range(5):
// 	try:
// 		print(abs(2-i) + abs(2-input().split().index("1")))
// 	except:
// 		pass
// 
// 
// 		
// 
// 
// 	
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(matrix: seq<seq<int>>) returns (output: string)
  requires |matrix| >= 5
{
  var result := 0;
  var i := 0;
  while i < 5
    invariant 0 <= i <= 5
    decreases 5 - i
  {
    var r := matrix[i];
    var idx := IndexOf1From3499(r, 0);
    if idx >= 0 {
      result := Abs3499(2 - i) + Abs3499(2 - idx);
    }
    i := i + 1;
  }
  output := IntToString(result) + "\n";
}

function IndexOf1From3499(r: seq<int>, i: int): int
  requires 0 <= i <= |r|
  decreases |r| - i
{
  if i >= |r| then -1
  else if r[i] == 1 then i
  else IndexOf1From3499(r, i + 1)
}

function Abs3499(x: int): int
{
  if x < 0 then -x else x
}
