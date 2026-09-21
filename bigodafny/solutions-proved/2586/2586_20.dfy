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

// Isolated multiplication: (i+1)*K == i*K + K.
lemma MulDistribAdd(i: int, K: int)
  ensures (i + 1) * K == i * K + K
{}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  // Loose scaffold: each outer step is bounded by the full inner range
  // `size` (== n*(n+1)/2, itself O(n**2)), not by the amortized argument
  // (each index of l2 fills at most once, so total inner work across all
  // outer iterations is also O(n**2)) that would give a tight O(n**2)
  // bound directly. This proof did not attempt that tighter argument.
  ensures steps <= 2 + (3 * (n * (n + 1) / 2) + 10) * n
{
  steps := 1;
  var size := n * (n + 1) / 2;
  var l2 := seq(size, _ => 0);
  var cost := 0;
  var i := 0;
  ghost var BOUND := 3 * size + 10;
  while i < n
    invariant 0 <= i <= n
    invariant |l2| == size
    invariant steps <= 1 + BOUND * i
    decreases n - i
  {
    ghost var iterBase := steps;
    var idx := a_list[i] - 1;
    if 0 <= idx < size {
      if l2[idx] == 0 {
        l2 := l2[idx := 1];
        steps := steps + 3;
      } else {
        var j := idx;
        ghost var jbase := steps + 2;
        steps := steps + 2;
        while j < size && l2[j] == 1
          invariant idx <= j
          invariant j <= size
          invariant |l2| == size
          invariant steps <= jbase + 2 * (j - idx)
          decreases size - j
        {
          cost := cost + 1;
          j := j + 1;
          steps := steps + 2;
        }
        if j < size {
          l2 := l2[j := 1];
        }
        steps := steps + 2;
      }
    }
    i := i + 1;
    steps := steps + 3;
    assert steps <= iterBase + BOUND;
    assert (i - 1 + 1) * BOUND == (i - 1) * BOUND + BOUND
      by { MulDistribAdd(i - 1, BOUND); }
  }
  output := IntToString(cost);
  steps := steps + 1;
}
