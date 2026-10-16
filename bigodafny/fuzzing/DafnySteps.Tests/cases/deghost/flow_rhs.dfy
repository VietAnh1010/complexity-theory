// A ghost local whose value flows into the counter becomes compiled.
method Solve(a: seq<int>) returns (output: int, ghost steps: nat)
{
  ghost var cost := |a| + 1;
  steps := cost;
  output := |a|;
}
