// Trace points: after each counter update, and first in each loop body.
method Solve(n: nat) returns (output: int, ghost steps: nat)
{
  steps := 0;
  var i := 0;
  while i < n {
    i := i + 1;
    steps := steps + 1;
  }
  for j := 0 to n {
    steps := steps + 2;
  }
  output := i;
}
