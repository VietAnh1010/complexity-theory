// 596_A. Wilbur and Swimming Pool  (problem 966, solution 966_54)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin
// n=int(stdin.readline().strip())
// s=[]
// for i in range(n):
//     
//     a,b=map(int,stdin.readline().strip().split())
//     s.append([a,b])
// ans=-1
// for i in range(n):
//     for j in range(i+1,n):
//         if( s[i][0]!=s[j][0] and  s[i][1]!=s[j][1] ):
//             
//             ans=abs(s[i][0]-s[j][0] )*  abs(s[i][1]-s[j][1] )  
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}


method Solve(n: int, values: seq<seq<string>>) returns (output: string)
{
  var xs: seq<int> := [];
  var ys: seq<int> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    xs := xs + [ParseInt(values[i][0])];
    ys := ys + [ParseInt(values[i][1])];
    i := i + 1;
  }
  var ans := -1;
  i := 0;
  while i < n
    decreases n - i
  {
    var j := i + 1;
    while j < n
      decreases n - j
    {
      if xs[i] != xs[j] && ys[i] != ys[j] {
        ans := AbsInt(xs[i] - xs[j]) * AbsInt(ys[i] - ys[j]);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  output := IntToString(ans);
}
