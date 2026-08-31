// 1041_A. Heist  (problem 603, solution 603_489)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n=int(input())
// indices=[]
// indices=input().split(' ')
// for i in range(n):
//     indices[i]=int(indices[i])
// minIndic=min(indices)
// maxIndic=max(indices)
// diff=maxIndic-minIndic+1
// if diff<n :
//     x=0
// else:
//     x=diff-n
// print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
