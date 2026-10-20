// 1 per operator and index, plus operands; literals and variables cost 0.

method Solve(a: seq<int>, i: nat, b: int)
    returns (output: int, ghost steps: nat)
{
  steps := 0;
  steps := steps + 3;
  var x := a[i] + b * 2;
  steps := steps + 1;
  var y := -x;
  var z := x;
  steps := steps + 2;
  output := x - y + z;
}
