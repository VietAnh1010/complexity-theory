// 1409_C. Yet Another Array Restoration  (problem 794, solution 794_215)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for _ in range(t):
//     n,x,y=list(map(int,input().split()))
//     d=y-x
//     for i in range(1,n):
//         if (y-x)%i==0:
//             d=min(d,(y-x)//i)
//     ans=[]
//     p=x
//     while p<=y and n>0:
//         ans.append(p)
//         p=p+d
//         n=n-1
//         if p>y:
//             break
//     p=x-d
//     while p>0 and n>0:
//         ans.append(p)
//         p=p-d
//         n=n-1
//     p=y+d
//     while n>0:
//         ans.append(p)
//         p=p+d
//         n=n-1
//     print(*ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, data: seq<(int, int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
