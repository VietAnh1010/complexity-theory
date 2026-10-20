// `a && b` charges b only when a lets it run; `||` and `==>` likewise.

method Solve(a: seq<int>, i: int)
    returns (output: bool, ghost steps: nat)
{
  steps := 0;
  steps := steps + (5 + if 0 <= i < |a| then 2 else 0);
  var p := 0 <= i < |a| && a[i] > 0;
  steps := steps + (2 + if i < 0 then 0 else 2);
  var q := i < 0 || a[i] == 0;
  steps := steps + 1;
  output := p ==> q;
}
