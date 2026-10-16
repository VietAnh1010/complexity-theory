// dafny 4.11.0.0
// Command Line Options: 
// call_out.dfy

method Solve(n: nat) returns (output: int, steps: nat)
{
  var r, s := Helper(n);
  steps := s + 1;
  print 0, steps;
  output := r;
}

method Helper(n: nat) returns (r: int, cost: nat)
{
  r := 2 * n;
  cost := 1;
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
