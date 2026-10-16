// A return statement returns the counter too.
method Solve(n: int) returns (output: int)
{
  if n < 0 {
    return 0;
  }
  return n + 1;
}
