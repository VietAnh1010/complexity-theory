// In the table, no rule needed: a let costs its right side plus its body, and
// keeps the binding when the body's cost mentions it; a tuple pattern costs
// its right side; a lambda value costs 0; `assert P; e` costs e.

method Solve(s: seq<int>, k: nat)
    returns (output: int, ghost steps: nat)
  requires k <= |s|
{
  steps := 0;
  steps := steps + (1 + var u := s[..k]; |u|);
  var doubled := var u := s[..k]; u + u;
  steps := steps + 3;
  var (p, q) := (1, |s| + 1);
  var f := (x: int) => x + 1;
  steps := steps + 3;
  output := assert k <= |s|; |doubled| + p + q;
}
