// 596_A. Wilbur and Swimming Pool  (problem 966, solution 966_134)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// x = []
// y = []
// for i in range(n):
//     xi, yi = map(int, input().split())
//     x.append(xi)
//     y.append(yi)
// if n==1:
//     print(-1)
// 
// if n>=2:
//     s = (max(x) - min(x)) * (max(y) - min(y))
//     if s == 0: s = -1
//     print(s)
//     
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
  if n == 1 {
    output := "-1";
  } else {
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
    var s := (MaxSeq(xs) - MinSeq(xs)) * (MaxSeq(ys) - MinSeq(ys));
    if s == 0 { s := -1; }
    output := IntToString(s);
  }
}
