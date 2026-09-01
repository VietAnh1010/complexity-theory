// 1107_C. Brutality  (problem 2083, solution 2083_142)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
// 	n, k = map(int, input().split())
// 	a = list(map(int, input().split()))
// 	s = input().strip()
// 	last = s[0]
// 	seg = [a[0]]
// 	all = []
// 	for i in range(1, len(s)):
// 		if last == s[i]:
// 			seg.append(a[i])
// 		else:
// 			last = s[i]
// 			all.append(seg)
// 			seg = [a[i]]
// 	if seg:
// 		all.append(seg)
// 	ans = 0
// 	for seg in all:
// 		if k < len(seg):
// 			seg = sorted(seg, reverse = True)[:k]
// 		ans += sum(seg)
// 	print(ans)
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d: string) returns (output: string)
{
  var k := b;
  var arr := c_list;
  var s := d;
  var last := s[0];
  var seg: seq<int> := [arr[0]];
  var allSegs: seq<seq<int>> := [];
  var i := 1;
  while i < |s|
    decreases |s| - i
  {
    if last == s[i] {
      seg := seg + [arr[i]];
    } else {
      last := s[i];
      allSegs := allSegs + [seg];
      seg := [arr[i]];
    }
    i := i + 1;
  }
  if |seg| > 0 {
    allSegs := allSegs + [seg];
  }
  var ans := 0;
  var si := 0;
  while si < |allSegs|
    decreases |allSegs| - si
  {
    var segv := allSegs[si];
    if k < |segv| {
      var sortedDesc := Sort(segv, (x: int, y: int) => x > y);
      segv := sortedDesc[..k];
    }
    ans := ans + SumSeq(segv);
    si := si + 1;
  }
  output := IntToString(ans);
}
