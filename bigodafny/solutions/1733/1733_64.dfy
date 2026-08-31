// 1427_D. Unshuffling a Deck  (problem 1733, solution 1733_64)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input=sys.stdin.readline
// n=int(input())
// c=list(map(int,input().split()))
// ac=[]
// f=int(n%2==1)
// for tar in range(1,n+1)[::-1]:
//     split=[]
//     cnt=0
//     if f:
//         for i in range(n):
//             cnt+=1
//             if tar<=c[i]:
//                 split.append(cnt)
//                 cnt=0
//     else:
//         for i in range(n)[::-1]:
//             cnt+=1
//             if tar<=c[i]:
//                 split.append(cnt)
//                 cnt=0
//     if cnt:
//         split.append(cnt)
//     if f==0:
//         split.reverse()
//     if len(split)==1:
//         f^=1
//         continue
//     ac.append(split)
//     new=[]
//     s=0
//     for i in range(len(split)):
//         new.append(c[s:s+split[i]])
//         s+=split[i]
//     new.reverse()
//     new_arr=[]
//     for tmp in new:
//         new_arr+=tmp
//     c=new_arr
//     f^=1
// print(len(ac))
// for arr in ac:
//     print(len(arr),*arr)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
