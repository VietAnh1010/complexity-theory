// 1342_B. Binary Period  (problem 662, solution 662_527)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # list( map(int, input().split()) )
// rw = int(input())
// for ewqr in range(rw):
//     t = input()
//     if t.count('1') == 0 or t.count('0') == 0:
//         print(t)
//         continue
//     s = '01' * len(t)
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, binary_strings: seq<string>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |binary_strings|
    invariant 0 <= i
    decreases n - i
  {
    var t := binary_strings[i];
    var c1 := CountChar(t, '1');
    var c0 := CountChar(t, '0');
    if c1 == 0 || c0 == 0 {
      parts := parts + [t + "\n"];
    } else {
      parts := parts + [Repeat("01", |t|) + "\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}

function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}
