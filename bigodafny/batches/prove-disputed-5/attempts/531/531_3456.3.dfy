include "../../prelude.dfy"
import opened Prelude

ghost function Len5(m: seq<seq<int>>, k: nat): nat
  requires k <= 5 <= |m|
  decreases k
{ if k == 0 then 0 else Len5(m, k - 1) + |m[k - 1]| }

lemma Len5Mono(m: seq<seq<int>>, a: nat, b: nat)
  requires a <= b <= 5 <= |m|
  ensures Len5(m, a) <= Len5(m, b)
  decreases b
{ if a < b { Len5Mono(m, a, b - 1); } }

method Solve(matrix: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires |matrix| >= 5
  ensures steps <= 2 * Len5(matrix, 5) + 60 + |output|
{
  steps := 1;
  var row := 1;
  var col := 1;
  var i := 0;
  var found := false;
  while i < 5 && !found
    invariant 0 <= i <= 5
    invariant steps <= 1 + 2 * Len5(matrix, i) + 12 * i
    decreases 5 - i
  {
    steps := steps + 2 * |matrix[i]| + 12;
    var r := matrix[i];
    if AllSame3456(r, 0) {
      row := row + 1;
    } else {
      col := IndexOf1From3456(r, 0) + 1;
      found := true;
    }
    i := i + 1;
  }
  output := IntToString(Abs3456(3 - row) + Abs3456(3 - col)) + "\n";
  Len5Mono(matrix, i, 5);
  ghost var v := Abs3456(3 - row) + Abs3456(3 - col);
  IntToStringDigits(v);
  steps := steps + Digits(v) + 6;
}

// Every r[j], j >= k, equals r[0].
function AllSame3456(r: seq<int>, k: nat): bool
  requires k <= |r|
  decreases |r| - k
{
  k == |r| || (r[k] == r[0] && AllSame3456(r, k + 1))
}

function IndexOf1From3456(r: seq<int>, i: int): int
  requires 0 <= i <= |r|
  decreases |r| - i
{
  if i >= |r| then -1
  else if r[i] == 1 then i
  else IndexOf1From3456(r, i + 1)
}

function Abs3456(x: int): int
{
  if x < 0 then -x else x
}
