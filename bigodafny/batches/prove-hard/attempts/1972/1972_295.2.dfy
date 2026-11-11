// --- Python ---------------------------------------------------------
// #!/usr/local/bin/python3
// 
// import sys
// 
// l, r, k = map(int, input().split())
// res = 1
// if k == 1: 
// 	if l == 1:
// 		print(1)
// 	else:
// 		print(-1)
// 	sys.exit()
// ans = 0
// while (res < l):
// 	res *= k;
// while (res <= r):
// 	print(res)
// 	ans += 1
// 	res *= k
// if ans == 0:
// 	print(-1)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(a: int, b: int, c: int)
    returns (output: string, ghost steps: nat)
  ensures steps <= 100 * (|output| + 1)
{
  steps := 0;
  var l := a;
  var r := b;
  var k := c;
  steps := steps + 1;
  if k == 1 {
    steps := steps + 1;
    if l == 1 {
      output := "1";
    } else {
      output := "-1";
    }
    return;
  }
  var res := 1;
  while res < l
    invariant k >= 2 ==> res >= 1
    invariant steps >= 0
    decreases if k >= 2 && res >= 1 then l - res else 0
  {
    steps := steps + 2;
    steps := steps + 1;
    res := res * k;
  }
  steps := steps + 1;
  var lines: seq<string> := [];
  var ans := 0;
  while res <= r
    invariant k >= 2 ==> res >= 1
    invariant steps >= 0
    decreases if k >= 2 && res >= 1 then r - res + 1 else 0
  {
    steps := steps + 2;
    steps := steps + (1 + Digits(res) + |[IntToString(res)]|);
    lines := lines + [IntToString(res)];
    steps := steps + 1;
    ans := ans + 1;
    steps := steps + 1;
    res := res * k;
  }
  steps := steps + 1;
  steps := steps + 1;
  if ans == 0 {
    output := "-1";
  } else {
    steps := steps + (SumLen(lines) + |lines|);
    output := Join(lines, "\n");
  }
}

import opened Prelude
