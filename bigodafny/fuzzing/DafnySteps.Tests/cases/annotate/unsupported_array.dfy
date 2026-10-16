// Without enable=arrays, allocating an array stops annotate.
method Solve(n: nat) returns (output: int)
{
  var a := new int[n];
  output := a.Length;
}
