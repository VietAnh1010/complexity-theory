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

// The binary search range [0, 10**12] is a literal in the source, not a
// function of n or |a_list|. Its iteration count is CeilLog2(10**12), a
// fixed constant -- O(1) -- per the "fixed in the source" convention.
ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  if n <= 1 { }
  else if m <= 1 { }
  else { CeilLog2Monotone((m + 1) / 2, (n + 1) / 2); }
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| > 0
  ensures steps <= 2 * |a_list| + 2 * CeilLog2(1000000000000) + 12
{
  steps := 1;
  var m := MaxSeq(a_list);
  steps := steps + |a_list|;
  var s := SumSeq(a_list);
  steps := steps + |a_list|;
  var beg := 0;
  var end := 1000000000000;
  steps := steps + 2;
  while beg < end - 1
    invariant 0 <= beg < end <= 1000000000000
    invariant steps <= 3 + 2 * |a_list| + 2 * (CeilLog2(1000000000000) - CeilLog2(end - beg))
    decreases end - beg
  {
    var mid := (beg + end) / 2;
    var w := end - beg;
    if n * mid - s >= mid && mid >= m {
      assert mid - beg == w / 2;
      end := mid;
    } else {
      assert end - mid == (w + 1) / 2;
      beg := mid;
    }
    CeilLog2Monotone(end - beg, (w + 1) / 2);
    steps := steps + 2;
  }
  output := IntToString(beg + 1);
  steps := steps + 1;
}
