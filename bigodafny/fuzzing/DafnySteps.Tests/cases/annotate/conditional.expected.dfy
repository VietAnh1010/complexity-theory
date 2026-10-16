
method Solve(a: seq<int>, c: bool)
    returns (output: int, ghost steps: nat)
{
  steps := 0;
  steps := steps + (1 + if c then 2 else 0);
  output := if c then a[0] + 1 else 0;
}
