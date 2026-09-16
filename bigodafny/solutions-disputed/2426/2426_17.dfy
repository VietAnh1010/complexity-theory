// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-batch-18
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The first while loop writes a := a[v := newVal] on every iteration
//     regardless of branch, and since a has length k (the number of
//     groups, up to 100) with no shrinking, this seq copy costs O(k) per
//     write; a run that completes close to all k iterations without r4
//     hitting 0 costs O(k**2), while Python's a[v] %= 4 style in-place
//     list write is O(1) per iteration and genuinely O(k).
//
//   how this label could be wrong, and what to check:
//     The label assumes a[v]:=newVal is O(1) as in Python's in-place
//     a[v]=... . Open the first while loop and confirm every iteration
//     does `a := a[v := newVal]`, a full seq copy; since that loop can run
//     through all |a| (=k, the group count) elements before r4 hits 0
//     (e.g. when each a[v]//4 stays small), the copy fires ~|a| times at
//     O(|a|) each, giving O(|a|**2). Check whether r4=n is large enough
//     relative to typical ai values that the loop rarely breaks early.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 49, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 2,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 839_B. Game of the Rows  (problem 2426, solution 2426_17)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k = map(int, input().split())
// 
// a = list(map(int,input().split()))
// all_sum = sum(a)
// r4,r2 = n,n*2
// for v in range(len(a)):
// 	mid = a[v] // 4
// 	a[v] = a[v] % 4
// 	if mid <= r4:
// 		r4 -= mid
// 	else:
// 		a[v] += 4 * (mid - r4)
// 		r4 = 0
// 	if r4 == 0:
// 		break
// mid = 0
// r22 = 0
// for v in a:
// 	if v % 2 == 1:
// 		mid += 1
// 	r22 += v // 2
// #print(r4,r22,mid,r2)
// if r4 > 0:
// 	mid -=r4
// 	r22 -= r4
// 	if mid < 0:
// 		r22 -= (mid // -2)
// 		mid = 0
// 
// if r22 + mid > r2:
// 	print('NO')
// else:
// 	print('YES')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, values: seq<int>) returns (output: string)
{
  var a := values;
  var r4 := n;
  var r2 := n * 2;
  var v := 0;
  while v < |a| && r4 != 0
    decreases |a| - v
  {
    var mid := FloorDiv(a[v], 4);
    var newVal := FloorMod(a[v], 4);
    if mid <= r4 {
      r4 := r4 - mid;
      a := a[v := newVal];
    } else {
      newVal := newVal + 4 * (mid - r4);
      r4 := 0;
      a := a[v := newVal];
    }
    v := v + 1;
  }

  var mid2 := 0;
  var r22 := 0;
  var j := 0;
  while j < |a|
    decreases |a| - j
  {
    if FloorMod(a[j], 2) == 1 {
      mid2 := mid2 + 1;
    }
    r22 := r22 + FloorDiv(a[j], 2);
    j := j + 1;
  }

  if r4 > 0 {
    mid2 := mid2 - r4;
    r22 := r22 - r4;
    if mid2 < 0 {
      r22 := r22 - FloorDiv(mid2, -2);
      mid2 := 0;
    }
  }

  if r22 + mid2 > r2 {
    output := "NO";
  } else {
    output := "YES";
  }
}
