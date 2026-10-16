// m.Keys, m.Values and m.Items charge |m|.
method Solve(m: map<int, int>) returns (output: set<int>)
{
  output := m.Keys + m.Values;
}
