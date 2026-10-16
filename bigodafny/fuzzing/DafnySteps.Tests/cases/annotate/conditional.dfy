// `if c then x else y`: 1, plus c, plus the branch taken.
method Solve(a: seq<int>, c: bool) returns (output: int)
{
  output := if c then a[0] + 1 else 0;
}
