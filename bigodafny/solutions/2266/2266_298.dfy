// 296_A. Yaroslav and Permutations  (problem 2266, solution 2266_298)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # your code goes here
// n=int(input())
// num=map(int,input().split())
// from collections import Counter
// freq=Counter(num)
// maximum=0
// for i in freq:
// 	if(maximum<freq[i]):
// 		maximum=freq[i]
// if(maximum <=((n+1)//2)):
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  var freq: map<string, int> := map[];
  var maximum := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var v := a_list[i];
    var c := if v in freq then freq[v] + 1 else 1;
    freq := freq[v := c];
    if c > maximum { maximum := c; }
    i := i + 1;
  }
  if maximum <= (n + 1) / 2 {
    output := "YES";
  } else {
    output := "NO";
  }
}
