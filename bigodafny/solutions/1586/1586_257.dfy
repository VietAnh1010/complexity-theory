// 433_A. Kitahara Haruki's Gift  (problem 1586, solution 1586_257)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=input()
// cnt={100:0, 200:0}
// w = list(map(int, input().split()))
// for i in w:
// 	cnt[i]+=1
// if cnt[100]&1 or (cnt[100]==0 and cnt[200]&1):
// 	print("NO")
// else:
// 	print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, scores: seq<int>) returns (output: string)
{
  var cnt100 := 0;
  var cnt200 := 0;
  var i := 0;
  while i < |scores|
    decreases |scores| - i
  {
    if scores[i] == 100 {
      cnt100 := cnt100 + 1;
    } else {
      cnt200 := cnt200 + 1;
    }
    i := i + 1;
  }
  if cnt100 % 2 != 0 || (cnt100 == 0 && cnt200 % 2 != 0) {
    output := "NO";
  } else {
    output := "YES";
  }
}
