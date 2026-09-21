// 346_A. Alice and Bob  (problem 1386, solution 1386_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
//
// n = int(input())
// arr = list(map(int, input().split()))
//
// gcd = 0
// for num in arr:
// 	gcd = math.gcd(gcd, num)
//
// moves = max(arr) / gcd - n
// if moves % 2:
// 	print('Alice')
// else:
// 	print('Bob')
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

method Solve(a: int, b_list: seq<int>) returns (output: string, ghost steps: nat)
  requires 1 <= a <= |b_list|
  requires forall k :: 0 <= k < |b_list| ==> b_list[k] >= 1
  ensures steps <= 5 * |b_list| + 10
{
  steps := 1;
  var n := a;
  var arr := b_list;
  var g := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant g >= 0
    invariant i > 0 ==> g > 0
    invariant steps <= 4 * i + 1
    decreases n - i
  {
    GcdPos(g, arr[i]);
    g := Gcd(g, arr[i]);
    i := i + 1;
    steps := steps + 4;
  }
  var mx := MaxSeq(arr);
  steps := steps + |arr|;
  var moves := FloorDiv(mx, g) - n;
  steps := steps + 2;
  output := if FloorMod(moves, 2) != 0 then "Alice" else "Bob";
  steps := steps + 1;
}
