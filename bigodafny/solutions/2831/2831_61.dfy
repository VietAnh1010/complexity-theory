// 769_B. News About Credit  (problem 2831, solution 2831_61)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// a = list(map(int, input().split()))
// 
// p = a[0]
// a = [(p, 0)] + sorted([(a[i], i) for i in range(1, n)], reverse=True)
// 
// result = ""
// 
// got = {0}
// 
// for i in range(n):
// 	temp_a = a[i][0]
// 	temp_i = i + 1
// 
// 	while temp_a > 0 and temp_i < n:
// 		if temp_i not in got:
// 			got.add(temp_i)
// 			temp_a -= 1
// 			result += str(a[i][1] + 1) + " " + str(a[temp_i][1] + 1) + "\n"
// 
// 		temp_i += 1
// 
// if len(got) < n:
// 	print(-1)
// else:
// 	print(n - 1)
// 	print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == n
  requires n >= 1
{
  var pairs: seq<(int,int)> := [];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |pairs| == i - 1
    decreases n - i
  {
    pairs := pairs + [(a_list[i], i)];
    i := i + 1;
  }
  var sorted := Sort(pairs, (x: (int,int), y: (int,int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  var a := [(a_list[0], 0)] + sorted;
  var got := seq(n, _ => false);
  var gotCount := 0;
  if n > 0 {
    got := got[0 := true];
    gotCount := 1;
  }
  var lines: seq<string> := [];
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant |got| == n
    invariant |a| == n
  {
    var temp_a := a[idx].0;
    var temp_i := idx + 1;
    while temp_a > 0 && temp_i < n
      invariant idx + 1 <= temp_i <= n
      invariant |got| == n
      decreases n - temp_i
    {
      if !got[temp_i] {
        got := got[temp_i := true];
        gotCount := gotCount + 1;
        temp_a := temp_a - 1;
        lines := lines + [IntToString(a[idx].1 + 1) + " " + IntToString(a[temp_i].1 + 1)];
      }
      temp_i := temp_i + 1;
    }
    idx := idx + 1;
  }
  if gotCount < n {
    output := "-1\n";
  } else {
    var rawResult := if |lines| > 0 then Join(lines, "\n") + "\n" else "";
    output := IntToString(n - 1) + "\n" + rawResult + "\n";
  }
}
