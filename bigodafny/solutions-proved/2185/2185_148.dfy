// 1091_B. New Year and the Treasure Geolocation  (problem 2185, solution 2185_148)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// p = []
// add = dict()
// for i in range(n):
// 	a, b = map(int, input().split())
// 	p.append((a, b))
// for i in range(n):
// 	a, b = map(int, input().split())	
// 	add[(a, b)] = 0
// for key in add.keys():
// 	T = [key[0] + p[0][0], key[1] + p[0][1]]
// 	ok = 1
// 	for i in range(1, n):
// 		if not ((T[0] - p[i][0], T[1] - p[i][1]) in add.keys()):
// 			ok = 0
// 	if ok == 1:
// 		print(*T)
// 		break		
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma Expand(n: nat)
  ensures n * (10 * n + 12) == 10 * (n * n) + 12 * n
{
}

method Solve(n: int, coord_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires 1 <= n && 2 * n <= |coord_list|
  requires forall k :: 0 <= k < |coord_list| ==> |coord_list[k]| >= 2
  ensures steps <= 10 * (n * n) + 30 * n + 12 + 2 * |output|
{
  steps := 3;
  var p := coord_list[0..n];
  var bset := coord_list[n..2*n];
  var addSet: set<(int,int)> := {};
  var idx := 0;
  while idx < |bset|
    invariant 0 <= idx <= |bset|
    invariant |bset| == n
    invariant steps <= 3 + 6 * idx
    decreases |bset| - idx
  {
    steps := steps + 6;
    addSet := addSet + {(bset[idx][0], bset[idx][1])};
    idx := idx + 1;
  }
  var foundT: (int,int) := (0,0);
  var found := false;
  idx := 0;
  ghost var s1 := steps;
  while idx < |bset| && !found
    invariant 0 <= idx <= |bset|
    invariant |bset| == n
    invariant steps <= s1 + idx * (10 * n + 12)
    decreases |bset| - idx
  {
    ghost var sA := steps;
    steps := steps + 12;
    var key := (bset[idx][0], bset[idx][1]);
    var T := (key.0 + p[0][0], key.1 + p[0][1]);
    var ok := true;
    var i := 1;
    ghost var s0 := steps;
    while i < n && ok
      invariant 1 <= i <= n || (i == 1 && n <= 1)
      invariant steps <= s0 + 10 * i
      decreases n - i
    {
      steps := steps + 10;
      var diff := (T.0 - p[i][0], T.1 - p[i][1]);
      if diff !in addSet { ok := false; }
      i := i + 1;
    }
    if ok {
      found := true;
      foundT := T;
    }
    idx := idx + 1;
    CostMulDistrib(idx - 1, 1, idx, 10 * n + 12);
  }
  CostMulMonoLeft(idx, n, 10 * n + 12);
  Expand(n);
  output := IntToString(foundT.0) + " " + IntToString(foundT.1);
  IntToStringDigits(foundT.0);
  IntToStringDigits(foundT.1);
  steps := steps + Digits(foundT.0) + 1 + Digits(foundT.1) + 1 + Digits(foundT.1);
}
