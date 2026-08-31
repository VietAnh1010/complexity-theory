// 158_B. Taxi  (problem 223, solution 223_180)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// g = int(input())
// j = list(map(int,input().split()))
// c = c1 = c2 = c3 = p= q = r = 0
// for i in j:
//     if(i==4):
//         c+=1
//     if(i==3):
//         c3+=1
//     if(i==2):
//         c2+=1
//     if(i==1):
//         c1+=1
// if(c1>c3):
//     p= c1-c3
//     c+=c3
// else:
//     c+=c3
// if(c2%2==0):
//     c+=(c2/2)
// else:
//     q=1
//     c+=((c2-1)/2)
// if(p != 0 or q!=0):
//     r = (p*1)+(q*2)
//     if(r//4==r/4):
//         c+=(r//4)
//     else:
//         c+=((r//4)+1)
// print(int(c))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var c := 0;
  var c1 := 0;
  var c2 := 0;
  var c3 := 0;
  var p := 0;
  var q := 0;
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    var v := a_list[idx];
    if v == 4 { c := c + 1; }
    if v == 3 { c3 := c3 + 1; }
    if v == 2 { c2 := c2 + 1; }
    if v == 1 { c1 := c1 + 1; }
    idx := idx + 1;
  }
  if c1 > c3 {
    p := c1 - c3;
    c := c + c3;
  } else {
    c := c + c3;
  }
  if c2 % 2 == 0 {
    c := c + c2 / 2;
  } else {
    q := 1;
    c := c + (c2 - 1) / 2;
  }
  if p != 0 || q != 0 {
    var r := p * 1 + q * 2;
    if r % 4 == 0 {
      c := c + r / 4;
    } else {
      c := c + (r / 4 + 1);
    }
  }
  output := IntToString(c);
}
