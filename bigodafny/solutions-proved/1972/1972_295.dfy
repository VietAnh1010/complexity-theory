// 614_A. Link/Cut Tree  (problem 1972, solution 1972_295)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../prelude.dfy"
import opened Prelude

ghost function Pow2(t: nat): nat
  decreases t
{
  if t == 0 then 1 else 2 * Pow2(t - 1)
}

ghost function Log2(x: nat): nat
  decreases x
{
  if x <= 1 then 0 else 1 + Log2(x / 2)
}

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

// If Pow2(t) <= x then t <= Log2(x): a doubling process that has reached x
// took at most Log2(x) doublings.
lemma Pow2LeImpliesLog2Ge(t: nat, x: nat)
  requires Pow2(t) <= x
  ensures t <= Log2(x)
  decreases t
{
  if t == 0 {
  } else {
    assert Pow2(t) == 2 * Pow2(t - 1);
    assert 2 * Pow2(t - 1) <= x;
    assert Pow2(t - 1) <= x / 2;
    Pow2LeImpliesLog2Ge(t - 1, x / 2);
  }
}

method Solve(a: int, b: int, c: int) returns (output: string, ghost steps: nat)
  requires a >= 1
  requires b >= 1
  requires c >= 1
  ensures steps <= 2 * Log2(a * c) + 6 * Log2(b * c) + |output| + 10
{
  var l := a;
  var r := b;
  var k := c;
  steps := 1;
  if k == 1 {
    if l == 1 {
      output := "1";
    } else {
      output := "-1";
    }
    steps := steps + 2;
    return;
  }
  var res := 1;
  ghost var cnt1 := 0;
  ghost var base1 := steps;
  while res < l
    invariant res >= 1
    invariant Pow2(cnt1) <= res
    invariant res <= l * k
    invariant steps <= base1 + 2 * cnt1
    decreases l - res
  {
    MulMonoRight(k, res, l - 1);
    res := res * k;
    MulMonoRight(Pow2(cnt1), 2, k);
    cnt1 := cnt1 + 1;
    steps := steps + 2;
  }
  assert Pow2(cnt1) <= l * k;
  Pow2LeImpliesLog2Ge(cnt1, l * k);
  var lines: seq<string> := [];
  var ans := 0;
  ghost var cnt2 := 0;
  ghost var base2 := steps;
  while res <= r
    invariant res >= 1
    invariant Pow2(cnt2) <= res
    invariant cnt2 == 0 || res <= r * k
    invariant |lines| == cnt2
    invariant steps <= base2 + 4 * cnt2 + |lines|
    decreases r - res
  {
    lines := lines + [IntToString(res)];
    ans := ans + 1;
    MulMonoRight(k, res, r);
    res := res * k;
    MulMonoRight(Pow2(cnt2), 2, k);
    cnt2 := cnt2 + 1;
    steps := steps + 4;
  }
  assert Pow2(cnt2) <= r * k;
  Pow2LeImpliesLog2Ge(cnt2, r * k);
  if ans == 0 {
    output := "-1";
  } else {
    output := Join(lines, "\n");
  }
  steps := steps + |output| + 3;
}
