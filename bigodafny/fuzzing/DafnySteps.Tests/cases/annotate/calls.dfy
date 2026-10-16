// A call to an annotated method adds its steps through a ghost lhs, in both
// statement forms. A call to the row's own function is charged 1 and noted.
function Twice(x: int): int { 2 * x }

method Solve(n: int) returns (output: int)
{
  var a := Helper(n);
  output := Helper(a + 1);
  output := output + Twice(n);
}

method Helper(x: int) returns (r: int)
{
  r := x + 1;
}
