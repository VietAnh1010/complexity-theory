// 546_B. Soldier and Badges  (problem 2586, solution 2586_20)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l1=list(map(int,input().split()))
// l2=[0]*int(n*(n+1)/2)
// cost=0
// for i in range (n):
//     if(l2[l1[i]-1]==0):
//         l2[l1[i]-1]=1
//     elif(l2[l1[i]-1]==1):
//         while(l2[l1[i]-1]==1):
//             cost+=1
//             l1[i]+=1
//         l2[l1[i]-1]=1
// print(cost)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
{
  var size := n * (n + 1) / 2;
  var l2 := seq(size, _ => 0);
  var cost := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |l2| == size
    decreases n - i
  {
    var idx := a_list[i] - 1;
    if 0 <= idx < size {
      if l2[idx] == 0 {
        l2 := l2[idx := 1];
      } else {
        var j := idx;
        while j < size && l2[j] == 1
          invariant idx <= j
          invariant |l2| == size
          decreases size - j
        {
          cost := cost + 1;
          j := j + 1;
        }
        if j < size {
          l2 := l2[j := 1];
        }
      }
    }
    i := i + 1;
  }
  output := IntToString(cost);
}
