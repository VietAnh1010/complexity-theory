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
