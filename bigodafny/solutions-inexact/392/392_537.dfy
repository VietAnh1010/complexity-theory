// 1223_B. Strings Equalization  (problem 392, solution 392_537)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// for i in range(0, n):
//     first_string = input()
//     second_string = input()
// 
//     map = {}
// 
//     for i in range(0, len(first_string)):
//         if first_string[i] in map:
//             map[first_string[i]]+=1
//         else:
//             map[first_string[i]] = 1
//     
//     same = False
// 
//     for i in range(0, len(second_string)):
//         if second_string[i] in map:
//             same = True
//             break
//     
//     if same == True:
//         print("YES")
//     else:
//         print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CharInString(s: string, c: char): bool
  decreases |s|
{
  if |s| == 0 then false
  else if s[0] == c then true
  else CharInString(s[1..], c)
}

function HasCommonChar(s: string, t: string): bool
  decreases |s|
{
  if |s| == 0 then false
  else if CharInString(t, s[0]) then true
  else HasCommonChar(s[1..], t)
}

method Solve(n: int, string_pairs: seq<(string, string)>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < |string_pairs|
    decreases |string_pairs| - i
  {
    if HasCommonChar(string_pairs[i].0, string_pairs[i].1) {
      lines := lines + ["YES"];
    } else {
      lines := lines + ["NO"];
    }
    i := i + 1;
  }
  output := Join(lines, "\n");
}
