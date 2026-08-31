// 1202_A. You Are Given Two Binary Strings...  (problem 88, solution 88_200)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for u in range(int(input())):
//     x=input()[::-1]
//     y=input()[::-1]
//     a,b=0,0
//     for i in range(len(y)):
//         if(y[i]=='1'):
//             a=i+1
//             break
//     for i in range(len(x)):
//         if(x[i]=='1' and i+1>=a):
//             b=i+1
//             break
//     print(b-a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_list: seq<string>) returns (output: string)
{
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    decreases n - t
  {
    var x := ReverseString(string_list[2 * t]);
    var y := ReverseString(string_list[2 * t + 1]);
    var a := 0;
    var i := 0;
    var found := false;
    while i < |y| && !found
      decreases |y| - i
    {
      if y[i] == '1' {
        a := i + 1;
        found := true;
      }
      i := i + 1;
    }
    var b := 0;
    var j := 0;
    var found2 := false;
    while j < |x| && !found2
      decreases |x| - j
    {
      if x[j] == '1' && j + 1 >= a {
        b := j + 1;
        found2 := true;
      }
      j := j + 1;
    }
    parts := parts + [IntToString(b - a)];
    t := t + 1;
  }
  output := Join(parts, "\n");
}

function ReverseString(s: string): string
  decreases |s|
{
  if |s| == 0 then s else ReverseString(s[1..]) + [s[0]]
}
