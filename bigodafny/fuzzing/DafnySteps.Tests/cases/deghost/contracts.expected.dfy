// dafny 4.11.0.0
// Command Line Options: 
// contracts.dfy

function Bound(n: nat): nat
{
  2 * n + 1
}

method Solve(n: int, a: seq<int>)
    returns (output: int, steps: nat, ghost extra: nat)
  requires n >= 0
  requires |a| == n && (n == 0 || a[0] > 0)
  ensures steps <= Bound(n)
  ensures extra == 0
  ensures output == n
{
  steps := 1;
  print 0, steps;
  extra := 0;
  output := n;
}

method TraceRequires(n: int, a: seq<int>) returns (ok: bool)
{
  ok := false;
  if n >= 0 {
    if |a| == n && (n == 0 || a[0] > 0) {
      ok := true;
    }
  }
}

method TraceBound(n: int, a: seq<int>, output: int, steps: nat)
    returns (ok: bool)
{
  ok := false;
  if steps <= Bound(n) {
    if output == n {
      ok := true;
    }
  }
}
