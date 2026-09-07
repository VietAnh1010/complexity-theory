// 330_B. Road Construction  (problem 698, solution 698_43)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// impassable = []
// 
// n,m = map(int,input().split())
// 
// for i in range(m):
// 	impassable.extend(list(map(int, input().split())))
// 
// center_candidates = [x for x in range(1,n+1) if x not in impassable]
// 
// center = center_candidates[-1]
// # min number of roads
// print(n-1)
// 
// for x in range(1,n+1):
// 	if x!=center:
// 		print (center, x)
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, q: int, queries: seq<seq<int>>) returns (output: string)
  requires n >= 1
{
  var removed := seq(n + 1, i requires 0 <= i < n + 1 => false);
  var qi := 0;
  while qi < q && qi < |queries|
    invariant 0 <= qi
    invariant |removed| == n + 1
    decreases q - qi
  {
    var row := queries[qi];
    var k := 0;
    while k < |row|
      invariant 0 <= k <= |row|
      invariant |removed| == n + 1
      decreases |row| - k
    {
      var x := row[k];
      if 1 <= x <= n {
        removed := removed[x := true];
      }
      k := k + 1;
    }
    qi := qi + 1;
  }
  var center := n;
  while center >= 1 && removed[center]
    invariant 0 <= center <= n
    decreases center
  {
    center := center - 1;
  }
  var parts: seq<string> := [IntToString(n - 1) + "\n"];
  var i := 1;
  while i <= n
    invariant 1 <= i
    decreases n - i
  {
    if i != center {
      parts := parts + [IntToString(center) + " " + IntToString(i) + "\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
