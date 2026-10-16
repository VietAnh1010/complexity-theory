// A call to an annotated method adds its steps through a ghost lhs, in both
// statement forms.
method Solve(n: int) returns (output: int)
{
  var a := Helper(n);
  output := Helper(a + 1);
  output := output + n;
}

method Helper(x: int) returns (r: int)
{
  r := x + 1;
}
