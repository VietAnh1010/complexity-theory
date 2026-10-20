
method Solve(n: int) returns (output: int, ghost steps: nat)
{
  steps := 0;
  var a, s0 := Helper(n);
  steps := steps + s0;
  steps := steps + 1;
  ghost var s1: nat;
  output, s1 := Helper(a + 1);
  steps := steps + s1;
  steps := steps + 1;
  output := output + n;
}

method Helper(x: int) returns (r: int, ghost steps: nat)
{
  steps := 0;
  steps := steps + 1;
  r := x + 1;
}
