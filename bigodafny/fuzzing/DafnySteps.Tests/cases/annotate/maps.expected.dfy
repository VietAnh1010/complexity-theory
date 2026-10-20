// m.Keys, m.Values and m.Items charge |m|.

method Solve(m: map<int, int>) returns (output: set<int>, ghost steps: nat)
{
  steps := 0;
  steps := steps + (1 + |m| + |m|);
  output := m.Keys + m.Values;
}
