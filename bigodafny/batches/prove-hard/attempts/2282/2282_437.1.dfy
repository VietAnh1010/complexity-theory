// --- Python ---------------------------------------------------------
// m, s = [int(a) for a in input().split()]
// maxx=""
// minn=""
// s1 = s
// s2 = s-1
// if s==0 and m==1: print(0, 0)
// elif s>9*m or s<1: print (-1, -1)
// elif m==1: print(s, s)
// else:
// 	for a in range(m):
// 		if s1>9:
// 			maxx+=str(9)
// 			s1-=9
// 		elif s1==0:
// 			maxx+=str(0)
// 		else:
// 			maxx+=str(s1)
// 			s1=0
// 	for a in range(m-1):
// 		if s2>9:
// 			minn=str(9)+minn
// 			s2-=9
// 		elif s2==0:
// 			minn=str(0)+minn
// 		else:
// 			minn=str(s2)+minn
// 			s2=0
// 	minn=str(s2+1)+minn
// 	print(minn, maxx)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma SqStep(a: nat)
  ensures (a + 1) * (a + 1) == a * a + 2 * a + 1
{
}

lemma SqPred(m: nat)
  requires m >= 1
  ensures (m - 1) * (m - 1) <= m * m
{
  CostMulMonoLeft(m - 1, m, m - 1);
  CostMulMono(m, m - 1, m);
}

method Solve(n: int, k: int)
    returns (output: string, ghost steps: nat)
  ensures steps <= (if n > 0 then n * n + 20 * n else 0) + 20 + 3 * |output|
{
  steps := 0;
  var m := n;
  var s := k;
  steps := steps + (2 + if s == 0 then 1 else 0);
  if s == 0 && m == 1 {
    output := "0 0";
  } else if s > 9 * m || s < 1 {
    output := "-1 -1";
  } else if m == 1 {
    IntToStringDigits(s);
    steps := steps + (Digits(s) + |" "| + Digits(s) + |IntToString(s)|);
    output := IntToString(s) + " " + IntToString(s);
  } else {
    var maxx := "";
    var s1 := s;
    var a := 0;
    while a < m
      invariant 0 <= a <= m
      invariant s1 >= 0
      invariant |maxx| == a
      invariant steps <= 3 + 6 * a
      decreases m - a
    {
      steps := steps + 2;
      steps := steps + 1;
      if s1 > 9 {
        steps := steps + |"9"|;
        maxx := maxx + "9";
        steps := steps + 1;
        s1 := s1 - 9;
      } else if s1 == 0 {
        steps := steps + |"0"|;
        maxx := maxx + "0";
      } else {
        IntToStringDigits(s1);
        assert Digits(s1) == 1;
        steps := steps + (Digits(s1) + |IntToString(s1)|);
        maxx := maxx + IntToString(s1);
        s1 := 0;
      }
      steps := steps + 1;
      a := a + 1;
    }
    steps := steps + 1;
    var minn := "";
    steps := steps + 1;
    var s2 := s - 1;
    a := 0;
    while a < m - 1
      invariant 0 <= a <= m - 1
      invariant s2 >= 0
      invariant |minn| == a
      invariant steps <= 5 + 6 * m + 6 * a + a * a
      decreases m - 1 - a
    {
      SqStep(a);
      steps := steps + 3;
      steps := steps + 1;
      if s2 > 9 {
        steps := steps + |minn|;
        minn := "9" + minn;
        steps := steps + 1;
        s2 := s2 - 9;
      } else if s2 == 0 {
        steps := steps + |minn|;
        minn := "0" + minn;
      } else {
        IntToStringDigits(s2);
        assert Digits(s2) == 1;
        steps := steps + (Digits(s2) + |minn|);
        minn := IntToString(s2) + minn;
        s2 := 0;
      }
      steps := steps + 1;
      a := a + 1;
    }
    steps := steps + 2;
    IntToStringDigits(s2 + 1);
    SqPred(m);
    steps := steps + (1 + Digits(s2 + 1) + |minn|);
    minn := IntToString(s2 + 1) + minn;
    steps := steps + (|" "| + |maxx|);
    output := minn + " " + maxx;
  }
}

import opened Prelude
