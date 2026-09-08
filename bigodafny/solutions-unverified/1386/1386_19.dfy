// 346_A. Alice and Bob  (problem 1386, solution 1386_19)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n = int(input())
// arr = sorted(list(map(int, input().split())))
// b = 0
// for i in arr:
//     b = math.gcd(b, i)
// c = (arr[0] - 1) // b
// c += sum([(arr[i+1] - arr[i] - 1) // b for i in range(n-1)])
// print('Bob' if c % 2 == 0 else 'Alice')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma GcdPos(x: int, y: int)
  requires x >= 0 && y >= 0 && (x > 0 || y > 0)
  ensures Gcd(x, y) > 0
  decreases y
{
  if y == 0 {
  } else {
    GcdPos(y, x % y);
  }
}

method Solve(a: int, b_list: seq<int>) returns (output: string)
  requires 1 <= a <= |b_list|
  requires forall k :: 0 <= k < |b_list| ==> b_list[k] >= 1
{
  var n := a;
  var arr := SortInts(b_list);
  SortIntsKeepsElems(b_list);
  assert forall k :: 0 <= k < |arr| ==> arr[k] >= 1 by {
    forall k | 0 <= k < |arr|
      ensures arr[k] >= 1
    {
      assert arr[k] in arr;
      assert arr[k] in b_list;
      var j :| 0 <= j < |b_list| && b_list[j] == arr[k];
    }
  }
  var g := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant g >= 0
    invariant i > 0 ==> g > 0
    decreases n - i
  {
    GcdPos(g, arr[i]);
    g := Gcd(g, arr[i]);
    i := i + 1;
  }
  var c := FloorDiv(arr[0] - 1, g);
  i := 0;
  while i < n - 1
    invariant 0 <= i
    decreases n - 1 - i
  {
    c := c + FloorDiv(arr[i+1] - arr[i] - 1, g);
    i := i + 1;
  }
  output := if FloorMod(c, 2) == 0 then "Bob" else "Alice";
}
