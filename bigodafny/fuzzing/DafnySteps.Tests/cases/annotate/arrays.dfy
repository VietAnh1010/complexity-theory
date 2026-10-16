// enable=arrays: new T[n] costs n, new T[n, m] n * m, new T[n](i => e) like
// seq(n, i => e), new T[] [a, b] like a display.
method Solve(n: nat, m: nat) returns (output: int)
{
  var a := new int[n];
  var grid := new int[n, m];
  var squares := new int[n](i => i * i);
  var small := new int[] [1, n, 3];
  output := a.Length + small[0];
}
