// dafny 4.11.0.0
// Command Line Options: 
// ghost_function.dfy

function Square(n: nat): nat
{
  n * n
}

function Cost(n: nat): nat
{
  Square(n) + 1
}

ghost function Unused(n: nat): nat
{
  n
}

method Solve(n: nat) returns (output: int, steps: nat)
{
  steps := Cost(n);
  print 0, steps;
  output := n;
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
