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

method Solve(n: int, coord_list: seq<seq<int>>) returns (output: string)
{
  var p := coord_list[0..n];
  var bset := coord_list[n..2*n];
  var addSet: set<(int,int)> := {};
  var idx := 0;
  while idx < |bset|
    decreases |bset| - idx
  {
    addSet := addSet + {(bset[idx][0], bset[idx][1])};
    idx := idx + 1;
  }
  var foundT: (int,int) := (0,0);
  var found := false;
  idx := 0;
  while idx < |bset| && !found
    decreases |bset| - idx
  {
    var key := (bset[idx][0], bset[idx][1]);
    var T := (key.0 + p[0][0], key.1 + p[0][1]);
    var ok := true;
    var i := 1;
    while i < n && ok
      decreases n - i
    {
      var diff := (T.0 - p[i][0], T.1 - p[i][1]);
      if diff !in addSet { ok := false; }
      i := i + 1;
    }
    if ok {
      found := true;
      foundT := T;
    }
    idx := idx + 1;
  }
  output := IntToString(foundT.0) + " " + IntToString(foundT.1);
}
