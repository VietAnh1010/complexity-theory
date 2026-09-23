// 801_A. Vicious Keyboard  (problem 2589, solution 2589_26)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// n=len(s)
// v=0
// k=0
// count=0
// flag=0
// fl=0
// for i in range(n):
// 	if(s[i]=='V' and not(i==len(s)-1)):
// 		if(s[i+1]=='K'):
// 			count+=1
// 			v=0
// 			k=0
// 			fl=1
// 		else:
// 			v+=1
// 			k=0
// 	elif(s[i]=='V' and (i==len(s)-1)):
// 		v+=1
// 	elif(fl==0 and s[i]=='K'):
// 		k+=1
// 	elif(fl==1 and s[i]=='K'):
// 		fl=0
// 	if((v>=2 or k>=2) and flag==0):
// 		count+=1
// 		flag=1
//
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string, ghost steps: nat)
  ensures steps <= 12 * |string_| + 3
{
  var s := string_;
  var n := |s|;
  var v := 0;
  var k := 0;
  var count := 0;
  var flag := false;
  var fl := false;
  var i := 0;
  steps := 2;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == n
    invariant steps <= 12 * i + 2
    decreases n - i
  {
    if s[i] == 'V' && i != n - 1 {
      if s[i + 1] == 'K' {
        count := count + 1;
        v := 0;
        k := 0;
        fl := true;
      } else {
        v := v + 1;
        k := 0;
      }
    } else if s[i] == 'V' && i == n - 1 {
      v := v + 1;
    } else if !fl && s[i] == 'K' {
      k := k + 1;
    } else if fl && s[i] == 'K' {
      fl := false;
    }
    steps := steps + 8;   // bounded number of s[i]/s[i+1] reads and comparisons
    if (v >= 2 || k >= 2) && !flag {
      count := count + 1;
      flag := true;
    }
    steps := steps + 2;
    i := i + 1;
    steps := steps + 2;
  }
  output := IntToString(count);
  steps := steps + 1;
}
