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
  output := ""; // TODO: translate the Python above
}
