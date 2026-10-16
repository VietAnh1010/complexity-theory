// An argument for a compiled in-parameter becomes compiled. Needs two rounds:
// Charge's c, then its k, then Solve's k.
method Solve(n: nat) returns (output: int, ghost steps: nat)
{
  ghost var k := 2 * n;
  steps := Charge(k);
  output := n;
}

method Charge(ghost k: nat) returns (ghost c: nat)
{
  c := k + 1;
}
