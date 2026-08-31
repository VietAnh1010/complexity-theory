// 1202_A. You Are Given Two Binary Strings...  (problem 88, solution 88_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for i in range(n):
// 	a=input()
// 	b=input()
// 	k=b[::-1].index("1")
// 	a=a[::-1]
// 	p=a[k::].index("1")
// 	print(p)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_list: seq<string>) returns (output: string)
{
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    decreases n - t
  {
    var a := string_list[2 * t];
    var b := string_list[2 * t + 1];
    var bRev := ReverseString(b);
    var k := 0;
    var found := false;
    var i := 0;
    while i < |bRev| && !found
      decreases |bRev| - i
    {
      if bRev[i] == '1' {
        k := i;
        found := true;
      }
      i := i + 1;
    }
    var aRev := ReverseString(a);
    var p := 0;
    var found2 := false;
    var j := k;
    while j < |aRev| && !found2
      decreases |aRev| - j
    {
      if aRev[j] == '1' {
        p := j - k;
        found2 := true;
      }
      j := j + 1;
    }
    parts := parts + [IntToString(p)];
    t := t + 1;
  }
  output := Join(parts, "\n");
}

function ReverseString(s: string): string
  decreases |s|
{
  if |s| == 0 then s else ReverseString(s[1..]) + [s[0]]
}
