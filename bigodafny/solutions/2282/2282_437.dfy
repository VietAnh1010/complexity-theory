// 489_C. Given Length and Sum of Digits...  (problem 2282, solution 2282_437)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m, s = [int(a) for a in input().split()]
// maxx=""
// minn=""
// s1 = s
// s2 = s-1
// if s==0 and m==1: print(0, 0)
// elif s>9*m or s<1: print (-1, -1)
// elif m==1: print(s, s)
// else:
// 	for a in range(m):
// 		if s1>9:
// 			maxx+=str(9)
// 			s1-=9
// 		elif s1==0:
// 			maxx+=str(0)
// 		else:
// 			maxx+=str(s1)
// 			s1=0
// 	for a in range(m-1):
// 		if s2>9:
// 			minn=str(9)+minn
// 			s2-=9
// 		elif s2==0:
// 			minn=str(0)+minn
// 		else:
// 			minn=str(s2)+minn
// 			s2=0
// 	minn=str(s2+1)+minn
// 	print(minn, maxx)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int) returns (output: string)
{
  var m := n;
  var s := k;
  if s == 0 && m == 1 {
    output := "0 0";
  } else if s > 9 * m || s < 1 {
    output := "-1 -1";
  } else if m == 1 {
    output := IntToString(s) + " " + IntToString(s);
  } else {
    var maxx := "";
    var s1 := s;
    var a := 0;
    while a < m
      decreases m - a
    {
      if s1 > 9 {
        maxx := maxx + "9";
        s1 := s1 - 9;
      } else if s1 == 0 {
        maxx := maxx + "0";
      } else {
        maxx := maxx + IntToString(s1);
        s1 := 0;
      }
      a := a + 1;
    }
    var minn := "";
    var s2 := s - 1;
    a := 0;
    while a < m - 1
      decreases (m - 1) - a
    {
      if s2 > 9 {
        minn := "9" + minn;
        s2 := s2 - 9;
      } else if s2 == 0 {
        minn := "0" + minn;
      } else {
        minn := IntToString(s2) + minn;
        s2 := 0;
      }
      a := a + 1;
    }
    minn := IntToString(s2 + 1) + minn;
    output := minn + " " + maxx;
  }
}
