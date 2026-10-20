// trace=6,11: only the loop at line 6 and the update at line 11 are traced.
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
