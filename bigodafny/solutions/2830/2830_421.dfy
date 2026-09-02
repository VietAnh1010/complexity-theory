// 746_B. Decoding  (problem 2830, solution 2830_421)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solution(n,s):
// 	ans = [" "]*n
// 
// 	if n%2==0:
// 		p = int(n/2) - 1
// 		for i in range(n):
// 			if i%2==0:
// 				ans[p - int(i/2) ] = s[i]
// 			else:
// 				ans[p + int((i+1)/2) ] = s[i]
// 	else:
// 		p = int(n/2)
// 		for i in range(n):
// 			if i%2==0:
// 				ans[p + int(i/2) ] = s[i]
// 			else:
// 				ans[p - int((i+1)/2) ] = s[i]	
// 	return ''.join(ans)
// 
// n = int(input())
// s = input()
// print(solution(n,s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  var sz := if n > 0 then n else 0;
  var buf := new char[sz];
  var k := 0;
  while k < n
    invariant 0 <= k <= sz
  {
    buf[k] := ' ';
    k := k + 1;
  }
  if n % 2 == 0 {
    var p := n / 2 - 1;
    var i := 0;
    while i < n
      invariant 0 <= i <= sz
    {
      var pos := if i % 2 == 0 then p - i / 2 else p + (i + 1) / 2;
      if 0 <= pos < n && i < |s| {
        buf[pos] := s[i];
      }
      i := i + 1;
    }
  } else {
    var p := n / 2;
    var i := 0;
    while i < n
      invariant 0 <= i <= sz
    {
      var pos := if i % 2 == 0 then p + i / 2 else p - (i + 1) / 2;
      if 0 <= pos < n && i < |s| {
        buf[pos] := s[i];
      }
      i := i + 1;
    }
  }
  output := buf[0..sz];
}
