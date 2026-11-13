include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, d: int, binary_list: seq<string>) returns (output: string, ghost steps: nat)
  requires 0 <= d < |binary_list|
  requires k <= |binary_list|
  ensures steps <= 10 * d + 10 * (if k > 0 then k else 0) + 30 + |output|
{
  steps := 1;
  var arr := binary_list;
  var len := |arr|;
  var count := 0;
  var i := 0;
  while i < d
    invariant 0 <= i <= d
    invariant steps <= 1 + 10 * i
    invariant |arr| == len
    decreases d - i
  {
    var pos := len - i - 1;
    if arr[pos] != "0" {
      count := count + 1;
      arr := arr[pos := "0"];
    }
    i := i + 1;
    steps := steps + 10;
  }
  i := i + 1;
  steps := steps + 0;
  var pos2 := len - d - 1;
  steps := steps + 4;
  if arr[pos2] == "0" {
    arr := arr[pos2 := "1"];
    count := count + 1;
    steps := steps + 4;
  }
  while i < k
    invariant d + 1 <= i <= (if k > d + 1 then k else d + 1)
    invariant steps <= 10 * i
    invariant |arr| == len
    decreases k - i
  {
    var pos3 := len - i - 1;
    if arr[pos3] != "0" {
      count := count + 1;
      arr := arr[pos3 := "0"];
    }
    i := i + 1;
    steps := steps + 10;
  }
  output := IntToString(count);
  IntToStringDigits(count);
  steps := steps + Digits(count) + 1;
}
