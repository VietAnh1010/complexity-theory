// 459_B. Pashmak and Flowers  (problem 669, solution 669_40)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// lst = list(map(int, input().split()))
// n=lst[0]
// b = list(map(int, input().split()))
// max=-1
// min=10000000000
// maxf=0
// minf=0
// for x in b:
//     if(x>max):
//         maxf=1
//         max=x
//     elif x==max:
//         maxf+=1
//     if(x<min):
//         minf=1
//         min=x
//     elif x==min:
//         minf+=1
// if(max==min):
//     print(max-min,maxf*(maxf-1)//2)
// else: 
//     print(max-min,maxf*minf)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
