// dafny 4.11.0.0
// Command Line Options: 
// call_in.dfy

method Solve(n: nat) returns (output: int, steps: nat)
{
  var k := 2 * n;
  steps := Charge(k);
  print 0, steps;
  output := n;
}

method Charge(k: nat) returns (c: nat)
{
  c := k + 1;
}

method TraceRequires(n: nat) returns (ok: bool)
{
  ok := false;
  ok := true;
}
