// 437_B. The Child and Set  (problem 1827, solution 1827_44)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import *
// 
// s, l = map(int, input().split())
// mL = floor(log2(l))
// mS = floor(log2(l))
// x = min(mL, mS)
// 
// S = []
// while x >= 0:
// 	a = 1
// 	while 2 ** x <= s and a * 2 ** x <= l:
// 		S.append(a * 2 ** x)
// 		a += 2
// 		s -= 2 ** x
// 	x -= 1
// if s == 0:
// 	print(len(S))
// 	print(' '.join(map(str, S)))
// else:
// 	print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Pow2(e: int): int
  requires e >= 0
  ensures Pow2(e) >= 1
  decreases e
{
  if e == 0 then 1 else 2 * Pow2(e - 1)
}

method Solve(a: int, b: int) returns (output: string)
  requires a >= 0
  requires b >= 1
{
  var s := a;
  var l := b;
  var x := 0;
  while Pow2(x + 1) <= l
    decreases l - Pow2(x + 1)
  {
    x := x + 1;
  }
  var S: seq<int> := [];
  var ss := s;
  var xx := x;
  while xx >= 0
    invariant ss >= 0
    decreases xx + 1
  {
    var aa := 1;
    while Pow2(xx) <= ss && aa * Pow2(xx) <= l
      invariant ss >= 0
      decreases ss
    {
      S := S + [aa * Pow2(xx)];
      aa := aa + 2;
      ss := ss - Pow2(xx);
    }
    xx := xx - 1;
  }
  if ss == 0 {
    output := IntToString(|S|) + "\n" + JoinInts(S, " ");
  } else {
    output := IntToString(-1);
  }
}
