// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n+m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-20
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     SumSeq(a_list) plus the nested while j < x loop together cost
//     O(|a_list| + total), where total is the sum of all ai values,
//     matching the Python's 'tree.extend([len(tree)] * x)' which is O(x)
//     per element and O(sum(a)) overall, so both are O(n+m) rather than
//     the labeled O(n).
//
//   how this label could be wrong, and what to check:
//     The label O(n) ignores that the inner while j < x loop's total
//     iterations across all i equal total = SumSeq(a_list), a second size
//     that the constraint 'sum of all ai does not exceed 2*10^5' lets grow
//     independent of |a_list|; check whether an input with small |a_list|
//     (few, large ai) still forces total (and thus arr's length and
//     JoinInts cost) to scale, which would confirm the missing +m term.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 49, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts", "SumSeq"], "loop_depth":
//     2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 901_A. Hashing Trees  (problem 2723, solution 2723_42)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def read():
// 	return tuple(int(x) for x in input().split())
// 
// def main():
// 	(h, ) = read()
// 	a = read()
// 	tree = []
// 	fi = 0
// 	flag = False
// 	for i, x in enumerate(a):
// 		if fi == 0:
// 			if not flag and x > 1:
// 				flag = True
// 			elif flag and x > 1:
// 				fi = len(tree)
// 			else:
// 				flag = False
// 		tree.extend([len(tree)] * x)
// 	if fi == 0:
// 		print('perfect')
// 		return
// 	else:
// 		print('ambiguous')
// 	print(' '.join(str(x) for x in tree))
// 	tree[fi] = fi - 1
// 	print(' '.join(str(x) for x in tree))
// 
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var total := SumSeq(a_list);
  if total < 0 { total := 0; }
  var arr := new int[total];
  var treeLen := 0;
  var fi := 0;
  var flag := false;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant 0 <= treeLen
  {
    var x := a_list[i];
    if fi == 0 {
      if !flag && x > 1 {
        flag := true;
      } else if flag && x > 1 {
        fi := treeLen;
      } else {
        flag := false;
      }
    }
    var batchVal := treeLen;
    var j := 0;
    while j < x
      invariant 0 <= j
    {
      if treeLen < total {
        arr[treeLen] := batchVal;
      }
      treeLen := treeLen + 1;
      j := j + 1;
    }
    i := i + 1;
  }
  if fi == 0 {
    output := "perfect\n";
  } else {
    var beforeSeq := arr[..];
    if 0 <= fi < total {
      arr[fi] := fi - 1;
    }
    var afterSeq := arr[..];
    output := "ambiguous\n" + JoinInts(beforeSeq, " ") + "\n" + JoinInts(afterSeq, " ") + "\n";
  }
}
