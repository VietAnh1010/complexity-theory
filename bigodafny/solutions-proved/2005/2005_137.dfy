// 1051_C. Vasya and Multisets  (problem 2005, solution 2005_137)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// n = int(input())
// s = list(map(int,input().split()))
// c = Counter(s)
// singles = [i for i in c if c[i]==1]
// multis = [i for i in c if c[i]>2]
// if len(singles)&1 and not multis:
//     print("NO")
// else:
//     print("YES")
//     sin,mul=len(singles)//2,len(singles)&1
//     ans = ""
//     for x in s:
//         if mul and c[x]>2:
//             mul-=1
//             ans+="A"
//         elif sin and c[x]==1:
//             sin-=1
//             ans+="A"
//         else:ans+="B"
//     print(ans)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 45 * |numbers| + |output| + 6
{
  steps := 1;
  var c: map<int, int> := map[];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |c| <= i
    invariant steps == 10 * i + 1
  {
    var v := numbers[i];
    c := c[v := (if v in c then c[v] else 0) + 1];
    i := i + 1;
    steps := steps + 10;
  }
  var singlesCount := 0;
  var multisNonEmpty := false;
  var keys := c.Keys;
  ghost var K := |c|;
  steps := steps + K;
  ghost var s0 := steps;
  while keys != {}
    invariant keys <= c.Keys
    invariant |keys| <= K
    invariant K <= |numbers|
    invariant steps == s0 + 14 * (K - |keys|)
    decreases |keys|
  {
    var key :| key in keys;
    if c[key] == 1 { singlesCount := singlesCount + 1; }
    if c[key] > 2 { multisNonEmpty := true; }
    keys := keys - {key};
    steps := steps + 14;
  }
  if singlesCount % 2 == 1 && !multisNonEmpty {
    output := "NO\n";
    steps := steps + 5;
  } else {
    var sin := singlesCount / 2;
    var mul := singlesCount % 2;
    var ansParts: seq<string> := [];
    var m := 0;
    ghost var s1 := steps;
    while m < |numbers|
      invariant 0 <= m <= |numbers|
      invariant |ansParts| == m
      invariant SumLen(ansParts) == m
      invariant steps == s1 + 16 * m
      decreases |numbers| - m
    {
      var x := numbers[m];
      var cx := if x in c then c[x] else 0;
      SumLenSnoc(ansParts, "A");
      SumLenSnoc(ansParts, "B");
      if mul > 0 && cx > 2 {
        mul := mul - 1;
        ansParts := ansParts + ["A"];
      } else if sin > 0 && cx == 1 {
        sin := sin - 1;
        ansParts := ansParts + ["A"];
      } else {
        ansParts := ansParts + ["B"];
      }
      m := m + 1;
      steps := steps + 16;
    }
    output := "YES\n" + Join(ansParts, "") + "\n";
    steps := steps + SumLen(ansParts) + |ansParts| + 3;
  }
}
