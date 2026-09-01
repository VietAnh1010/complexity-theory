// 1547_B. Alphabetical Strings  (problem 2087, solution 2087_50)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for _ in range(int(input())):
//     a=input()
//     s=""
//     while  len(a)!=1:
//         if a[0]>a[-1]:
//             s+=a[0]
//             a=a[1:]
//         else:
//             s+=a[-1]
//             a=a[:-1]
// 
//         if len(a)==1:
//             break
//     s+="a"
//     if a!="a" or s[::-1] not in "abcdefghijklmnopqrstuvwxyz":
//         print("NO")
//     else:
//         print("YES")
//             
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(strings: seq<string>) returns (output: string)
{
  var alphabet := "abcdefghijklmnopqrstuvwxyz";
  var results: seq<string> := [];
  var si := 0;
  while si < |strings|
    decreases |strings| - si
  {
    var a := strings[si];
    var s := "";
    while |a| != 1
      decreases |a|
    {
      if a[0] > a[|a| - 1] {
        s := s + [a[0]];
        a := a[1..];
      } else {
        s := s + [a[|a| - 1]];
        a := a[..|a| - 1];
      }
    }
    s := s + "a";
    var rev: string := seq(|s|, i requires 0 <= i < |s| => s[|s| - 1 - i]);
    var found := false;
    var start := 0;
    while start + |rev| <= |alphabet| && !found
      decreases |alphabet| - start
    {
      if alphabet[start..start + |rev|] == rev {
        found := true;
      }
      start := start + 1;
    }
    if a != "a" || !found {
      results := results + ["NO"];
    } else {
      results := results + ["YES"];
    }
    si := si + 1;
  }
  output := Join(results, "\n");
}
