
method Solve(n: int) returns (output: int, ghost steps: nat)
{
  steps := 0;
  steps := steps + 1;
  if n < 0 {
    return 0, steps;
  }
  steps := steps + 1;
  return n + 1, steps;
}
