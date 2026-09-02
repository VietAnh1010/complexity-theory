// 432_B. Football Kit  (problem 378, solution 378_20)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// x=[]
// for i in range(n):
//     x.append(list(map(int,input().split())))
//  
// h={}
// a={}
// for i in range(n):
//     if(h.get(str(x[i][0]))):
//         h[str(x[i][0])]+=1
//     else:
//         h[str(x[i][0])]=1
//     
// for i in range(n):
//     home=n-1
//     if(h.get(str(x[i][1]))):
//         if(h[str(x[i][1])]>0):
//             away= n-1-h[str(x[i][1])]
//             home+=h[str(x[i][1])]
//     else:
//         away=n-1
//     print(home,away)   
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

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string)
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
{
  var h: map<int, int> := map[];
  var idx := 0;
  while idx < |pairs|
    decreases |pairs| - idx
  {
    var home0 := ParseInt(pairs[idx][0]);
    if home0 in h {
      h := h[home0 := h[home0] + 1];
    } else {
      h := h[home0 := 1];
    }
    idx := idx + 1;
  }
  var lines: seq<string> := [];
  idx := 0;
  while idx < |pairs|
    decreases |pairs| - idx
  {
    var away0 := ParseInt(pairs[idx][1]);
    var home := n - 1;
    var away := n - 1;
    if away0 in h {
      var cnt := h[away0];
      away := n - 1 - cnt;
      home := home + cnt;
    }
    lines := lines + [IntToString(home) + " " + IntToString(away)];
    idx := idx + 1;
  }
  output := Join(lines, "\n");
}
