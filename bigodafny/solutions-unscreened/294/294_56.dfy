// p03687 AtCoder Grand Contest 016 - Shrinking  (problem 294, solution 294_56)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// exitLower = list(set(list(s)))
// m = len(s)
// 
// for alp in exitLower:
//     SL = list(s)
//     cnt = 0
//     while len(set(SL)) > 1:
//         for i in range(len(SL)-1):
//             if SL[i+1] == alp:
//                 SL[i] = alp
//         SL.pop()
//         cnt += 1
//     m = min(m,cnt)
// 
// print(m)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var seen: set<char> := {};
  var distinct: seq<char> := [];
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] !in seen {
      seen := seen + {s[i]};
      distinct := distinct + [s[i]];
    }
    i := i + 1;
  }
  var m := |s|;
  var k := 0;
  while k < |distinct|
    decreases |distinct| - k
  {
    var cnt := ShrinkCount(s, distinct[k]);
    if cnt < m { m := cnt; }
    k := k + 1;
  }
  output := IntToString(m);
}

method AllSameChar(s: string) returns (r: bool)
{
  r := true;
  var i := 1;
  while i < |s|
    decreases |s| - i
  {
    if s[i] != s[0] { r := false; }
    i := i + 1;
  }
}

method ShrinkCount(s0: string, alp: char) returns (cnt: int)
{
  var SL := s0;
  cnt := 0;
  var same := AllSameChar(SL);
  while !same
    decreases |SL|
  {
    var tmp: seq<char> := [];
    var i := 0;
    while i < |SL| - 1
      decreases |SL| - 1 - i
    {
      if SL[i + 1] == alp {
        tmp := tmp + [alp];
      } else {
        tmp := tmp + [SL[i]];
      }
      i := i + 1;
    }
    SL := tmp;
    cnt := cnt + 1;
    same := AllSameChar(SL);
  }
}
