// A while body: 1 plus the guard per iteration; after the loop, the guard's
// failing evaluation. A for body: 1 per iteration.

method Solve(a: seq<int>) returns (output: int, ghost steps: nat)
{
  steps := 0;
  var i := 0;
  output := 0;
  while i < |a| && a[i] != 0 {
    steps := steps + (4 + if i < |a| then 2 else 0);
    steps := steps + 2;
    output := output + a[i];
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + (3 + if i < |a| then 2 else 0);
  steps := steps + 1;
  for j := 0 to |a| {
    steps := steps + 1;
    steps := steps + 1;
    output := output + 1;
  }
}
