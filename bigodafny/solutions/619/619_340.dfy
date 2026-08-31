// 975_A. Aramic script  (problem 619, solution 619_340)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = list(input().split())
// dic = dict()
// for i in s:
//     l2 = list(set(list(i)))
//     l2.sort()
//     l2 = ''.join(l2)
//     if l2 in dic:
//         pass
//     else:
//         dic[l2] = 1
// c = 0
// #print(dic)
// for i in dic:
//     c+=1
// print(c)
//     
//         
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var sigs: seq<string> := [];
  var i := 0;
  while i < |strings|
    decreases |strings| - i
  {
    var sg := Signature619(strings[i]);
    sigs := sigs + [sg];
    i := i + 1;
  }
  var distinctCount := CountDistinct619(sigs);
  output := IntToString(distinctCount);
}

method Signature619(s: string) returns (sig: string)
{
  var pres := seq(26, _ => false);
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    var idx := (s[i] as int) - ('a' as int);
    if 0 <= idx < 26 {
      pres := pres[idx := true];
    }
    i := i + 1;
  }
  var alphabet := "abcdefghijklmnopqrstuvwxyz";
  sig := "";
  i := 0;
  while i < 26
    decreases 26 - i
  {
    if pres[i] {
      sig := sig + [alphabet[i]];
    }
    i := i + 1;
  }
}

method CountDistinct619(xs: seq<string>) returns (c: int)
{
  var seen: seq<string> := [];
  var i := 0;
  while i < |xs|
    decreases |xs| - i
  {
    if xs[i] !in seen {
      seen := seen + [xs[i]];
    }
    i := i + 1;
  }
  c := |seen|;
}
