// dafny 4.11.0.0
// Command Line Options: 
// flow_rhs.dfy

method Solve(a: seq<int>) returns (output: int, steps: nat)
{
  var cost := |a| + 1;
  steps := cost;
  print 0, steps;
  output := |a|;
}

method TraceRequires(a: seq<int>) returns (ok: bool)
{
  ok := false;
  ok := true;
}
