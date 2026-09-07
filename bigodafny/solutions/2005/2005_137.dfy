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

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var sorted := SortInts(numbers);
  var distinct: seq<int> := [];
  var counts: seq<int> := [];
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |distinct| == |counts|
  {
    var v := sorted[i];
    var j := i;
    while j < |sorted| && sorted[j] == v
      invariant i <= j <= |sorted|
    { j := j + 1; }
    distinct := distinct + [v];
    counts := counts + [j - i];
    i := j;
  }
  var singlesCount := 0;
  var multisNonEmpty := false;
  var k := 0;
  while k < |counts|
  {
    if counts[k] == 1 { singlesCount := singlesCount + 1; }
    if counts[k] > 2 { multisNonEmpty := true; }
    k := k + 1;
  }
  if singlesCount % 2 == 1 && !multisNonEmpty {
    output := "NO\n";
  } else {
    var sin := singlesCount / 2;
    var mul := singlesCount % 2;
    var ansParts: seq<string> := [];
    var m := 0;
    while m < |numbers|
    {
      var x := numbers[m];
      var lo := 0;
      var hi := |distinct|;
      while lo < hi
        invariant 0 <= lo <= hi <= |distinct|
      {
        var mid := (lo + hi) / 2;
        if distinct[mid] == x { lo := mid; hi := mid; }
        else if distinct[mid] < x { lo := mid + 1; }
        else { hi := mid; }
      }
      var cx := if lo < |distinct| && distinct[lo] == x then counts[lo] else 0;
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
    }
    output := "YES\n" + Join(ansParts, "") + "\n";
  }
}
