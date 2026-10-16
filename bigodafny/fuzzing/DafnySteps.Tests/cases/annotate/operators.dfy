// 1 per operator and index, plus operands; literals and variables cost 0.
method Solve(a: seq<int>, i: nat, b: int) returns (output: int)
{
  var x := a[i] + b * 2;
  var y := -x;
  var z := x;
  output := x - y + z;
}
