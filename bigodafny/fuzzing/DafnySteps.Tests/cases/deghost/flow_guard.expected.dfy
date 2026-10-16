// dafny 4.11.0.0
// Command Line Options: 
// flow_guard.dfy

method Solve(n: int) returns (output: int, steps: nat)
{
  var big := n > 10;
  steps := 1;
  print 0, steps;
  if big {
    steps := steps + 2;
    print 1, steps;
  }
  output := n;
}

method TraceRequires(n: int) returns (ok: bool)
{
  ok := false;
  ok := true;
}

method TraceBound(n: int, output: int, steps: nat)
    returns (ok: bool)
{
  ok := false;
  ok := true;
}
