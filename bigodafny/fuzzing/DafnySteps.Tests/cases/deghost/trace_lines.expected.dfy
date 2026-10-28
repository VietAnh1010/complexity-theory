// dafny 4.11.0.0
// Command Line Options: 
// trace_lines.dfy

method Solve(n: nat) returns (output: int, steps: nat)
{
  steps := 0;
  var i := 0;
  while i < n {
    print 0, steps;
    i := i + 1;
    steps := steps + 1;
  }
  for j := 0 to n {
    steps := steps + 2;
    print 1, steps;
  }
  output := i;
}

method TraceRequires(n: nat) returns (ok: bool)
{
  ok := false;
  ok := true;
}
