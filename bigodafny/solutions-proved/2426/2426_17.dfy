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

method Solve(n: int, m: int, values: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 12 * |values| + 10
{
  steps := 1;
  var a := values;
  var r4 := n;
  var r2 := n * 2;
  var v := 0;
  while v < |a| && r4 != 0
    invariant 0 <= v <= |a|
    invariant |a| == |values|
    invariant steps <= 1 + 6 * v
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
    steps := steps + 6;
  }

  ghost var steps1 := steps;
  var mid2 := 0;
  var r22 := 0;
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant |a| == |values|
    invariant steps == steps1 + 6 * j
    decreases |a| - j
  {
    if FloorMod(a[j], 2) == 1 {
      mid2 := mid2 + 1;
    }
    r22 := r22 + FloorDiv(a[j], 2);
    j := j + 1;
    steps := steps + 6;
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
  steps := steps + 3;
}
