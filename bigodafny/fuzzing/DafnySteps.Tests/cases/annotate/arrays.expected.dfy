
method Solve(n: nat, m: nat)
    returns (output: int, ghost steps: nat)
{
  steps := 0;
  steps := steps + n;
  var a := new int[n];
  steps := steps + n * m;
  var grid := new int[n, m];
  steps := steps + 2 * n;
  var squares := new int[n] (i => i * i);
  steps := steps + 3;
  var small := new int[] [1, n, 3];
  steps := steps + 3;
  output := a.Length + small[0];
}
