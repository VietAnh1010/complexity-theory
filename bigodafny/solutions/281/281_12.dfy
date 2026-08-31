// 389_A. Fox and Number Game  (problem 281, solution 281_12)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = eval(input())
// no = list(map(eval,input().split()))
// while True:
//     flag = False
//     for i in no:
//         if i<=0:
//             continue
//         for j in range(n):
//             if no[j]>i:
//                 flag = True
//                 if no[j]%i == 0:
//                     no[j] = i
//                 else:
//                     no[j] = no[j]%i
//     if flag == False:
//         break
// # print(no)
// sum = 0
// for i in no:
//     sum += i
// print(int(sum))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  decreases *
{
  var no := a_list;
  var flag := true;
  while flag
    decreases *
  {
    flag := false;
    var oi := 0;
    while oi < n
      decreases n - oi
    {
      var iv := no[oi];
      if iv > 0 {
        var j := 0;
        while j < n
          decreases n - j
        {
          if no[j] > iv {
            flag := true;
            if no[j] % iv == 0 {
              no := no[j := iv];
            } else {
              no := no[j := no[j] % iv];
            }
          }
          j := j + 1;
        }
      }
      oi := oi + 1;
    }
  }
  var total := 0;
  var k := 0;
  while k < |no|
    decreases |no| - k
  {
    total := total + no[k];
    k := k + 1;
  }
  output := IntToString(total);
}
