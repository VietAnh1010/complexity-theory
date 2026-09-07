// 814_A. An abandoned sentiment from past  (problem 101, solution 101_10)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// l=list(map(int,input().split()))
// k=list(sorted(map(int,input().split()),reverse=True))
// for i in range(n):
//     if l[i]==0:
//         l[i]=k[0]
//         k.pop(0)
// if l==sorted(l):
//     print("No")
// else:
//     print("Yes")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  var kSorted := Sort(b_list, (x: int, y: int) => x > y);
  var l := a_list;
  var ptr := 0;
  var i := 0;
  while i < n && i < |l|
    invariant 0 <= i
    invariant |l| == |a_list|
    invariant 0 <= ptr
    decreases n - i
  {
    if l[i] == 0 {
      if ptr < |kSorted| {
        l := l[i := kSorted[ptr]];
        ptr := ptr + 1;
      }
    }
    i := i + 1;
  }
  if l == SortInts(l) {
    output := "No\n";
  } else {
    output := "Yes\n";
  }
}
