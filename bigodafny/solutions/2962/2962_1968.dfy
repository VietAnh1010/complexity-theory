// 141_A. Amusing Joke  (problem 2962, solution 2962_1968)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=input()
// l=input()
// m=input()
// a=len(n)+len(l)
// c=0
// n=list(n)+list(l)
// m=list(m)
// d=[]
// d=d+m
// for i in range(len(n)):
//     if n[i] not in m:
//         c=1
//         break
//     else:
//         d.remove(n[i])
//         m.remove(n[i])
// if c==1:
//     print("NO")
// elif len(d)!=0:
//     print("NO")
// else:
//     print("YES")
//             
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(first_name: seq<string>, second_name: seq<string>, jumbled_name: seq<string>) returns (output: string)
{
  var need := first_name + second_name;
  var remaining := jumbled_name;
  var c := 0;
  var i := 0;
  while i < |need| && c == 0
    invariant 0 <= i <= |need|
    decreases |need| - i
  {
    var ch := need[i];
    var idx := -1;
    var j := 0;
    while j < |remaining|
      invariant 0 <= j <= |remaining|
      invariant idx == -1 || (0 <= idx < j && remaining[idx] == ch)
      decreases |remaining| - j
    {
      if idx == -1 && remaining[j] == ch { idx := j; }
      j := j + 1;
    }
    if idx == -1 {
      c := 1;
    } else {
      remaining := remaining[..idx] + remaining[idx + 1..];
    }
    i := i + 1;
  }
  if c == 1 {
    output := "NO";
  } else if |remaining| != 0 {
    output := "NO";
  } else {
    output := "YES";
  }
}
