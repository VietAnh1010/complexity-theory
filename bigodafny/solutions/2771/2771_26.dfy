// 56_B. Spoilt Permutation  (problem 2771, solution 2771_26)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = [0]+list(map(int, input().split()))
// l, r = -1, -1
// i = 0
// while(i<n and arr[i]+1==arr[i+1]):
//     i+=1
// l = i
// i+=1
// while(i<n and arr[i]-1==arr[i+1]):
//     i+=1
//     r = i
// i+=1
// while(i<n and arr[i]+1==arr[i+1]):
//     i+=1
// if(r != -1 and i>= n-1):
//     print(l+1, r)
// else:
//     print(0, 0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
