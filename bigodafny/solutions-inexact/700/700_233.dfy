// 447_B. DZY Loves Strings  (problem 700, solution 700_233)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// k=int(input())
// w=list(map(int,input().split()))
// score=0
// for i in range(len(s)):
//     score+=(w[ord(s[i])-97]*(i+1))
// 
// score=score+(max(w)*(k*len(s)+(k*(k+1)//2)))
// print(int(score))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string)
{
  var total := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    var idx := (s[i] as int) - 97;
    total := total + a_list[idx] * (i + 1);
    i := i + 1;
  }
  var mx := MaxSeq(a_list);
  total := total + mx * (n * |s| + (n * (n + 1)) / 2);
  output := IntToString(total);
}
