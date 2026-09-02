// 611_B. New Year and Old Property  (problem 1364, solution 1364_163)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def z(n):
//     n = bin(n)[2:]
//     k = len(n)
//     s = (k-1) * (k-2) // 2 + (n.count("0") == 1)
//     r = n.find("0")
//     s += k if r == -1 else r
//
//     return s - 1;
//
// a, b = map(int, input().split());
// print (z(b) - z(a - 1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ToBinary(n: int): string
  requires n >= 0
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else ToBinary(n / 2) + (if n % 2 == 0 then "0" else "1")
}

function CountZeros(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == '0' then 1 else 0) + CountZeros(s[1..])
}

function FindZero(s: string): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == '0' then 0
  else (var r := FindZero(s[1..]); if r == -1 then -1 else r + 1)
}

function Z(n: int): int
  requires n >= 0
{
  var bs := ToBinary(n);
  var k := |bs|;
  var s := (k - 1) * (k - 2) / 2 + (if CountZeros(bs) == 1 then 1 else 0);
  var r := FindZero(bs);
  var s2 := s + (if r == -1 then k else r);
  s2 - 1
}

method Solve(a: int, b: int) returns (output: string)
{
  output := IntToString(Z(b) - Z(a - 1));
}
