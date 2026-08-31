// 1005_E1. Median on Segments (Permutations Edition)  (problem 1332, solution 1332_41)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// p=list(map(int,input().split()))
// cur=0
// while p[cur]!=m:
//     cur+=1
// pos=cur
// s={}
// cnt,len=0,0
// while cur>=0:
//     if p[cur]<=m:
//         cnt+=1
//     len+=1
//     if 2*cnt-len in s:
//         s[2*cnt-len]+=1
//     else:
//         s[2*cnt-len]=1
//     cur-=1
// cur=pos
// cnt,len,ans=0,0,0
// while cur<n:
//     if p[cur]<=m:
//         cnt+=1
//     len+=1
//     if len-2*cnt+1 in s:
//         ans+=s[len-2*cnt+1]
//     if len-2*cnt+2 in s:
//         ans+=s[len-2*cnt+2]
//     cur+=1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
