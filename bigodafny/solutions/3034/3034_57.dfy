// 1150_C. Prefix Sum Primes  (problem 3034, solution 3034_57)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// y=list(map(int,input().split()))
// if n==1:
//     print(y[0])
// else:
//     even=y.count(2)
//     odd=y.count(1)
//     if even==0 or odd==0:
//         print(*y)
//     else:
//         y=sorted(y)
//         y.reverse()
//         i=0
//         while i<n:
//             if y[i]==1:
//                 break
//             i+=1
//         t=y[i]
//         y[i]=y[1]
//         y[1]=t
//         print(*y)
//         
//                 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var y := a_list;
  if |y| == 0 {
    output := "";
    return;
  }
  if n == 1 {
    output := IntToString(y[0]);
    return;
  }
  var even := 0;
  var odd := 0;
  var i := 0;
  while i < |y|
    invariant 0 <= i <= |y|
    decreases |y| - i
  {
    if y[i] == 2 {
      even := even + 1;
    } else if y[i] == 1 {
      odd := odd + 1;
    }
    i := i + 1;
  }
  if even == 0 || odd == 0 {
    output := JoinInts(y, " ");
    return;
  }
  var sorted := Sort(y, (a: int, b: int) => a > b);
  i := 0;
  while i < |sorted| && sorted[i] != 1
    invariant 0 <= i <= |sorted|
    decreases |sorted| - i
  {
    i := i + 1;
  }
  if i >= |sorted| || |sorted| < 2 {
    output := JoinInts(sorted, " ");
    return;
  }
  var t := sorted[i];
  sorted := sorted[i := sorted[1]];
  sorted := sorted[1 := t];
  output := JoinInts(sorted, " ");
}
