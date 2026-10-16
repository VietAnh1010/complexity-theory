// `x, s := M(..)` with s compiled: M's out-parameter at s's position becomes
// compiled, whatever its name.
method Solve(n: nat) returns (output: int, ghost steps: nat)
{
  var r, s := Helper(n);
  steps := s + 1;
  output := r;
}

method Helper(n: nat) returns (r: int, ghost cost: nat)
{
  r := 2 * n;
  cost := 1;
}
