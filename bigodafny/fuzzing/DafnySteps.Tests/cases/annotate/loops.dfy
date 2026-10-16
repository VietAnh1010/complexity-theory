// A while body: 1 plus the guard per iteration; after the loop, the guard's
// failing evaluation. A for body: 1 per iteration.
method Solve(a: seq<int>) returns (output: int)
{
  var i := 0;
  output := 0;
  while i < |a| && a[i] != 0 {
    output := output + a[i];
    i := i + 1;
  }
  for j := 0 to |a| {
    output := output + 1;
  }
}
