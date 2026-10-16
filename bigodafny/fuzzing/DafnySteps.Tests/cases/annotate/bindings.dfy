// In the table, no rule needed: a let costs its right side plus its body, and
// keeps the binding when the body's cost mentions it; a tuple pattern costs
// its right side; a lambda value costs 0; `assert P; e` costs e.
method Solve(s: seq<int>, k: nat) returns (output: int)
  requires k <= |s|
{
  var doubled := (var u := s[..k]; u + u);
  var (p, q) := (1, |s| + 1);
  var f := (x: int) => x + 1;
  output := (assert k <= |s|; |doubled| + p + q);
}
