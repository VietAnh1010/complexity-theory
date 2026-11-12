// 279_A. Point on Spiral  (problem 2847, solution 2847_21)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x, y = map(int, input().split())
// 
// cur_x, cur_y = 0, 0
// i = 1
// pos = 0
// sign = [(1, 0), (0, 1), (-1, 0), (0, -1)]
// ans = 0
// j = 0
// while cur_x != x or cur_y != y:
//      if j == i:
//           j = 0
//           if pos % 2 == 1:
//                i += 1
//           pos = (pos + 1) % 4
//           ans += 1     
//      
//      cur_x = cur_x + sign[pos][0]
//      cur_y = cur_y + sign[pos][1]
//      j += 1
// 
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function SpL(k: nat): nat { k / 2 + 1 }

ghost function SpS(k: nat): nat
  decreases k
{
  if k == 0 then 0 else SpS(k - 1) + SpL(k - 1)
}

ghost function SpFX(k: nat, j: int): int {
  if k % 4 == 0 then j - k / 4
  else if k % 4 == 1 then k / 4 + 1
  else if k % 4 == 2 then k / 4 + 1 - j
  else -(k / 4 + 1)
}

ghost function SpFY(k: nat, j: int): int {
  if k % 4 == 0 then -(k / 4)
  else if k % 4 == 1 then j - k / 4
  else if k % 4 == 2 then k / 4 + 1
  else k / 4 + 1 - j
}

ghost function SpDX(p: int): int {
  if p == 0 then 1 else if p == 2 then -1 else 0
}

ghost function SpDY(p: int): int {
  if p == 1 then 1 else if p == 3 then -1 else 0
}

ghost function SpAbs(x: int): nat { if x < 0 then -x else x }

ghost function SpR(a: int, b: int): nat {
  if SpAbs(a) >= SpAbs(b) then SpAbs(a) else SpAbs(b)
}

ghost function SpK0(a: int, b: int): nat {
  var R: int := SpR(a, b);
  if R == 0 then 0
  else if b == -R && a > -R then 4 * R
  else if a == R then 4 * (R - 1) + 1
  else if b == R then 4 * (R - 1) + 2
  else 4 * (R - 1) + 3
}

ghost function SpJ0(a: int, b: int): nat {
  var R: int := SpR(a, b);
  if R == 0 then 0
  else if b == -R && a > -R then a + R
  else if a == R then b + R - 1
  else if b == R then R - a
  else R - b
}

ghost function SpTarget(a: int, b: int): nat {
  SpS(SpK0(a, b)) + SpJ0(a, b)
}

lemma SpSeam(k: nat)
  ensures SpFX(k, SpL(k)) == SpFX(k + 1, 0)
  ensures SpFY(k, SpL(k)) == SpFY(k + 1, 0)
{
}

lemma SpStep(k: nat, j: int)
  ensures SpFX(k, j + 1) == SpFX(k, j) + SpDX(k % 4)
  ensures SpFY(k, j + 1) == SpFY(k, j) + SpDY(k % 4)
{
}

lemma SpSMono(k: nat, k2: nat)
  requires k < k2
  ensures SpS(k) + SpL(k) <= SpS(k2)
  decreases k2
{
  if k2 > k + 1 { SpSMono(k, k2 - 1); }
}

lemma SpSInc(k: nat, k2: nat)
  requires k < k2
  ensures SpS(k) < SpS(k2)
{
  SpSMono(k, k2);
}

lemma SpInjLt(k: nat, j: nat, k2: nat, j2: nat)
  requires k < k2 && j <= SpL(k) && j2 <= SpL(k2)
  requires SpS(k) + j == SpS(k2) + j2
  ensures SpFX(k, j) == SpFX(k2, j2) && SpFY(k, j) == SpFY(k2, j2)
{
  SpSMono(k, k2);
  if k2 > k + 1 { SpSInc(k + 1, k2); }
  SpSeam(k);
}

lemma SpInj(k: nat, j: nat, k2: nat, j2: nat)
  requires j <= SpL(k) && j2 <= SpL(k2)
  requires SpS(k) + j == SpS(k2) + j2
  ensures SpFX(k, j) == SpFX(k2, j2) && SpFY(k, j) == SpFY(k2, j2)
{
  if k < k2 { SpInjLt(k, j, k2, j2); }
  else if k2 < k { SpInjLt(k2, j2, k, j); }
}

lemma SpTargetOK(a: int, b: int)
  ensures SpJ0(a, b) <= SpL(SpK0(a, b))
  ensures SpFX(SpK0(a, b), SpJ0(a, b)) == a
  ensures SpFY(SpK0(a, b), SpJ0(a, b)) == b
{
}

lemma SpTargetReach(k: nat, j: nat, a: int, b: int)
  requires j <= SpL(k)
  requires SpS(k) + j == SpTarget(a, b)
  ensures SpFX(k, j) == a && SpFY(k, j) == b
{
  SpTargetOK(a, b);
  SpInj(k, j, SpK0(a, b), SpJ0(a, b));
}

method Solve(a: int, b: int) returns (output: string)
{
  var x := a; var y := b;
  var curX := 0; var curY := 0;
  var i := 1;
  var pos := 0;
  var signX := [1, 0, -1, 0];
  var signY := [0, 1, 0, -1];
  var ans := 0;
  var j := 0;
  ghost var k: nat := 0;
  SpTargetOK(a, b);
  while curX != x || curY != y
    invariant 0 <= pos < 4
    invariant x == a && y == b
    invariant 0 <= j <= i && i == SpL(k) && pos == k % 4 && ans == k
    invariant signX == [1, 0, -1, 0] && signY == [0, 1, 0, -1]
    invariant curX == SpFX(k, j) && curY == SpFY(k, j)
    invariant SpS(k) + j <= SpTarget(a, b)
    decreases SpTarget(a, b) - (SpS(k) + j)
  {
    if SpS(k) + j == SpTarget(a, b) { SpTargetReach(k, j, a, b); }
    if j == i {
      SpSeam(k);
      k := k + 1;
      j := 0;
      if pos % 2 == 1 { i := i + 1; }
      pos := (pos + 1) % 4;
      ans := ans + 1;
    }
    SpStep(k, j);
    assert signX[pos] == SpDX(pos) && signY[pos] == SpDY(pos);
    curX := curX + signX[pos];
    curY := curY + signY[pos];
    j := j + 1;
  }
  output := IntToString(ans);
}
