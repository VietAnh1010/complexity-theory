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
  output := ""; // TODO: translate the Python above
}
