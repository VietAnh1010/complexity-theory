// p03957 CODE FESTIVAL 2016 qual C - CF  (problem 493, solution 493_134)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N=input()
// c=0
// flag = 0
// for i in N:
//     if i=='C' and  c==0 :c+=1
//     if i=='F' and c==1: flag=1
// if flag==1:print("Yes")
// else :print("No")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  var c := 0;
  var flag := 0;
  var i := 0;
  while i < |string_|
    decreases |string_| - i
  {
    if string_[i] == 'C' && c == 0 {
      c := 1;
    }
    if string_[i] == 'F' && c == 1 {
      flag := 1;
    }
    i := i + 1;
  }
  output := (if flag == 1 then "Yes" else "No") + "\n";
}
