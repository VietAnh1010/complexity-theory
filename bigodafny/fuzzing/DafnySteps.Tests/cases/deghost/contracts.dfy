// TraceRequires and TraceBound compile Solve's contract. An ensures naming a
// ghost out (extra) is left out of TraceBound; Bound becomes compiled.
// TraceBoundValue returns the right-hand side of `steps <= Bound(n)`.
ghost function Bound(n: nat): nat { 2 * n + 1 }

method Solve(n: int, a: seq<int>) returns (output: int, ghost steps: nat, ghost extra: nat)
  requires n >= 0
  requires |a| == n && (n == 0 || a[0] > 0)
  ensures steps <= Bound(n)
  ensures extra == 0
  ensures output == n
{
  steps := 1;
  extra := 0;
  output := n;
}
