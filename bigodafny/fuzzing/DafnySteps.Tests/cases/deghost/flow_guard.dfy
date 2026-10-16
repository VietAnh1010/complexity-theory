// The guard around a counter update becomes compiled, with the ghost it reads.
method Solve(n: int) returns (output: int, ghost steps: nat)
{
  ghost var big := n > 10;
  steps := 1;
  if big {
    steps := steps + 2;
  }
  output := n;
}
