// A compiled `:|` other than picking from a set is not in the cost model.
method Solve(a: seq<int>, k: int) returns (output: int)
  requires k in a
{
  var m :| 0 <= m < |a| && a[m] == k;
  output := m;
}
