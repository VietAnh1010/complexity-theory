// dafny 4.11.0.0
// Command Line Options: 
// trace_points.dfy

method Solve(n: nat) returns (output: int, steps: nat)
{
  steps := 0;
  print 0, steps;
  var i := 0;
  while i < n {
    print 1, steps;
    i := i + 1;
    steps := steps + 1;
    print 4, steps;
  }
  for j := 0 to n {
    print 2, steps;
    steps := steps + 2;
    print 3, steps;
  }
  output := i;
}

method TraceRequires(n: nat) returns (ok: bool)
{
  ok := false;
  ok := true;
}

method TraceBound(n: nat, output: int, steps: nat)
    returns (ok: bool)
{
  ok := false;
  ok := true;
}
