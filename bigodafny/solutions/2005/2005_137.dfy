// 1051_C. Vasya and Multisets  (problem 2005, solution 2005_137)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// n = int(input())
// s = list(map(int,input().split()))
// c = Counter(s)
// singles = [i for i in c if c[i]==1]
// multis = [i for i in c if c[i]>2]
// if len(singles)&1 and not multis:
//     print("NO")
// else:
//     print("YES")
//     sin,mul=len(singles)//2,len(singles)&1
//     ans = ""
//     for x in s:
//         if mul and c[x]>2:
//             mul-=1
//             ans+="A"
//         elif sin and c[x]==1:
//             sin-=1
//             ans+="A"
//         else:ans+="B"
//     print(ans)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
