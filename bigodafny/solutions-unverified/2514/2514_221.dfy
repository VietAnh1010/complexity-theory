// 1084_B. Kvass and the Fair Nut  (problem 2514, solution 2514_221)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = list(map(int,input().split()))
// s = n[1]
// n = n[0]
// a = list(map(int,input().split()))
// 
// a = sorted(a,reverse = True)
// k = min(a)
// su = 0
// if s > sum(a):
//     print(-1)
// else:
//     for i in range(len(a)):
//         if a[i] > k:
//             su += (a[i]-k)
//             a[i] = k
//             if su >= s:
//                 break
//     if su < s:
//         k = (n*k-(s-su))//n
//         print(k)
//     else:
//         print(k)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>) returns (output: string)
{
  var arr := Sort(c_list, (x: int, y: int) => x > y);
  var kk := MinSeq(c_list);
  var su := 0;
  var total := SumSeq(c_list);
  if b > total {
    output := "-1";
  } else {
    var i := 0;
    while i < |arr| && su < b
      decreases |arr| - i
    {
      if arr[i] > kk {
        su := su + (arr[i] - kk);
        arr := arr[i := kk];
      }
      i := i + 1;
    }
    if su < b {
      var res := FloorDiv(a * kk - (b - su), a);
      output := IntToString(res);
    } else {
      output := IntToString(kk);
    }
  }
}
