// 348_A. Mafia  (problem 1626, solution 1626_33)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// """
// Code of Ayush Tiwari
// Codeforces: servermonk
// Codechef: ayush572000
// 
// """
// import sys
// input = sys.stdin.buffer.readline
// 
// def solution():
//     n=int(input())
//     l=list(map(int,input().split()))
//     beg=0
//     end=10**12
//     m=max(l)
//     s=sum(l)
//     while beg<end-1:
//         mid=(beg+end)//2
//         if n*mid-s>=mid and mid>=m:
//             end=mid
//         else:
//             beg=mid
//     print(beg+1)
// 
// solution()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
