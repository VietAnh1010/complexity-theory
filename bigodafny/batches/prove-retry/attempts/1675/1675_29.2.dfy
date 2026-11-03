include "../../prelude.dfy"
import opened Prelude

ghost function Pending(s: string, c: char, i: int): nat
{
  if exists p :: i <= p < |s| && s[p] == c then 0 else 1
}

method Solve(v0: string, v1: string) returns (output: string, ghost steps: nat)
  requires |v0| >= 1
{
  steps := 1;
  var s := v0;
  var t := v1;
  var i := 0;
  var j := 0;
  var nt := 0;
  var ar := 0;
  var at := 0;
  var done := false;
  while i <= |s| && j < |t| && !done
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |t|
    invariant |s| == |v0|
    decreases |t| - j, !done, Pending(s, t[j], i), |s| - i
  {
    if i == |s| {
      i := 0;
      ar := 1;
    }
    var found := false;
    var idx := 0;
    while idx < |s|
      invariant 0 <= idx <= |s|
      invariant found <==> exists q :: 0 <= q < idx && s[q] == t[j]
      decreases |s| - idx
    {
      if s[idx] == t[j] {
        found := true;
      }
      idx := idx + 1;
    }
    if found {
      if s[i] == t[j] {
        s := s[i := ':'];
        j := j + 1;
        i := i + 1;
      } else {
        i := i + 1;
        at := 1;
      }
    } else {
      nt := 1;
      done := true;
    }
  }
  if nt == 0 && |s| == |t| {
    at := 0;
  } else {
    at := 1;
  }
  if nt == 1 {
    output := "need tree";
  } else if at == 1 && ar == 1 {
    output := "both";
  } else if at == 1 {
    output := "automaton";
  } else if ar == 1 {
    output := "array";
  } else {
    output := "";
  }
}
