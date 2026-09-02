// 245_A. System Administrator  (problem 2719, solution 2719_94)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// num=eval(input())
// alist=[]
// for i in range(num):
//     a=input()
//     b=a.split()
//     c=[int(x) for x in b]
// 
//     alist.append(c)
// 
// 
// geshua=0
// geshub=0
// zongshua=0
// zongshub=0
// for k in alist:
//     if k[0]==1:
//         geshua=geshua+1
//         zongshua=zongshua+k[1]
//     else:
//         geshub=geshub+1
//         zongshub=zongshub+k[1]
// 
// if zongshua>=geshua*5:
//     print("LIVE")
// else:
//     print('DEAD')
// if zongshub>=geshub*5:
//     print("LIVE")
// else:
//     print('DEAD')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values_list: seq<seq<int>>) returns (output: string)
{
  var geshua := 0; var geshub := 0; var zongshua := 0; var zongshub := 0;
  var i := 0;
  while i < |values_list|
    invariant 0 <= i <= |values_list|
  {
    var row := values_list[i];
    if |row| >= 2 {
      if row[0] == 1 {
        geshua := geshua + 1;
        zongshua := zongshua + row[1];
      } else {
        geshub := geshub + 1;
        zongshub := zongshub + row[1];
      }
    }
    i := i + 1;
  }
  var line1 := if zongshua >= geshua * 5 then "LIVE" else "DEAD";
  var line2 := if zongshub >= geshub * 5 then "LIVE" else "DEAD";
  output := line1 + "\n" + line2;
}
