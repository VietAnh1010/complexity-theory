// 59_B. Fortune Telling  (problem 384, solution 384_34)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// f = int(input())
// petals = list(map(int,input().split()))
// #print(f'suma: {sum(petals)}')
// while True:
//     if sum(petals)%2 == 1:
//         print(sum(petals))
//         break
//     else:
//         try:
//             m = min(i for i in petals if i%2)
//         except:
//             m = min(petals)
//         #print(f'removed: {m} ')
//         petals.remove(m)
//         #print(sum(petals))
//         #print(petals)
//     if petals == []:
//         print(0)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
