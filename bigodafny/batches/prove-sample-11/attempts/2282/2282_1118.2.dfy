// 489_C. Given Length and Sum of Digits...  (problem 2282, solution 2282_1118)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m,s=map(int,input().split())
//  
// def ismax(m,s):
//     op1=str()
//     if s==0:
//         return(-1)
//     elif s>m*9:
//         return(-1)
//     else:
//         for i in range(m):
//             if s>9:
//                 op1=op1+'9'
//                 s-=9
//             elif 0<s<=9:
//                 op1=op1+str(s)
//                 s=0
//             else:
//                 op1=op1+'0'
//         return(int(op1))
// 
// def ismin(m,s):
//     op2=str()
//     lis=[]
//     if s==0:
//         return(-1)
//     elif s>m*9:
//         return(-1)
//     else:
//         l=max(1,s-9*(m-1))
//         op2=op2+str(l)
//         s=s-l
//         for i in range(m-1):
//             if s>9:
//                 lis.append(9)
//                 s-=9
//             elif 0<s<=9:
//                 lis.append(s)
//                 s=0
//             else:
//                 lis.append(0)
//         lis=sorted(lis)
//         if len(lis)==1:
//             op2=op2+str(*lis)
//         elif len(lis)>1:
//             st="".join(map(str,lis))
//             op2=op2+st
//         return(int(op2))
// if m==1 and s==0:
//     print(0, 0)
// else:
//     print(ismin(m,s),ismax(m,s))
//     
//                 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude


function Mp(m: int): nat { if m > 0 then m else 0 }

ghost function CostMax(m: int, s: int): nat
  decreases Mp(m)
{
  if m <= 0 then 1
  else if s > 9 then Mp(m - 1) + 6 + CostMax(m - 1, s - 9)
  else if 0 < s && s <= 9 then Mp(m - 1) + 6 + CostMax(m - 1, 0)
  else Mp(m - 1) + 6 + CostMax(m - 1, s)
}

ghost function CostMinRec(m: int, s: int): nat
  decreases Mp(m)
{
  if m <= 0 then 1
  else if s > 9 then Mp(m - 1) + 6 + CostMinRec(m - 1, s - 9)
  else if 0 < s && s <= 9 then Mp(m - 1) + 6 + CostMinRec(m - 1, 0)
  else Mp(m - 1) + 6 + CostMinRec(m - 1, s)
}

lemma QuadStep(k: nat)
  ensures k * k + 6 * k + 1 + k + 6 <= (k + 1) * (k + 1) + 6 * (k + 1) + 1
{
}

lemma MaxLen(m: int, s: int)
  ensures |BuildMaxDigits1118(m, s)| <= Mp(m)
  ensures CostMax(m, s) <= Mp(m) * Mp(m) + 6 * Mp(m) + 1
  decreases Mp(m)
{
  if m > 0 {
    if s > 9 { MaxLen(m - 1, s - 9); }
    else if 0 < s && s <= 9 { MaxLen(m - 1, 0); IntToStringDigits(s); }
    else { MaxLen(m - 1, s); }
    QuadStep(Mp(m - 1));
  }
}

lemma MinLen(m: int, s: int)
  ensures |BuildMinDigits1118(m, s)| <= Mp(m)
  ensures CostMinRec(m, s) <= Mp(m) * Mp(m) + 6 * Mp(m) + 1
  decreases Mp(m)
{
  if m > 0 {
    if s > 9 { MinLen(m - 1, s - 9); }
    else if 0 < s && s <= 9 { MinLen(m - 1, 0); }
    else { MinLen(m - 1, s); }
    QuadStep(Mp(m - 1));
  }
}

ghost function MaxCharge(m: int, s: int): nat
  requires m >= 0
{
  if s == 0 || s > m * 9 then 5 else 5 + CostMax(m, s)
}

lemma MaxCostBound(m: int, s: int)
  requires m >= 0
  ensures MaxCharge(m, s) <= m * m + 6 * m + 6
{
  if !(s == 0 || s > m * 9) { MaxLen(m, s); }
}

ghost function MinCharge(m: int, s: int): nat
  requires m >= 0
{
  if s == 0 || s > m * 9 then 5
  else
    var l := if 1 > s - 9 * (m - 1) then 1 else s - 9 * (m - 1);
    var lis := BuildMinDigits1118(m - 1, s - l);
    8 + Digits(l) + CostMinRec(m - 1, s - l) + SortCost(|lis|) + |lis|
      + SumDigits(SortInts(lis)) + SumDigits(SortInts(lis))
}

lemma MinCostBound(m: int, s: int)
  requires m >= 0
  ensures MinCharge(m, s) <= m * m + 6 * m + 20 + 2 * NLogN(m) + 3 * |IsMin1118(m, s)|
{
  if !(s == 0 || s > m * 9) {
    var l := if 1 > s - 9 * (m - 1) then 1 else s - 9 * (m - 1);
    var lis := BuildMinDigits1118(m - 1, s - l);
    MinLen(m - 1, s - l);
    SortIntsIsSorted(lis);
    SortCostWithin(|lis|, m);
    IntToStringDigits(l);
    SortIntsIsSorted(lis);
    if |lis| > 0 { JoinIntsLen(SortInts(lis), ""); }
    else { assert |SortInts(lis)| == 0; }
    assert Mp(m - 1) <= m;
    assert |lis| <= m;
    var k := Mp(m - 1);
    CostMulMonoLeft(k, m, k);
    CostMulMono(m, k, m);
    assert |IsMin1118(m, s)| == Digits(l) + SumDigits(SortInts(lis));
  }
}

method Solve(n: int, k: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 3 * (n * n) + 2 * NLogN(n) + 40 * n + 40 + 6 * |output|
{
  steps := 1;
  var m := n;
  var s := k;
  steps := steps + 3;
  if m == 1 && s == 0 {
    output := "0 0";
    steps := steps + 1;
  } else {
    var mn := IsMin1118(m, s);
    var mx := IsMax1118(m, s);
    output := mn + " " + mx;
    MaxCostBound(m, s);
    MinCostBound(m, s);
    steps := steps + MinCharge(m, s) + MaxCharge(m, s) + 1 + |mx|;
    assert |mn| <= |output| && |mx| <= |output|;
  }
}

function IsMax1118(m: int, s: int): string
  requires m >= 0
{
  if s == 0 then "-1"
  else if s > m * 9 then "-1"
  else BuildMaxDigits1118(m, s)
}

function BuildMaxDigits1118(m: int, s: int): string
  decreases if m > 0 then m else 0
{
  if m <= 0 then ""
  else if s > 9 then "9" + BuildMaxDigits1118(m - 1, s - 9)
  else if 0 < s && s <= 9 then IntToString(s) + BuildMaxDigits1118(m - 1, 0)
  else "0" + BuildMaxDigits1118(m - 1, s)
}

function IsMin1118(m: int, s: int): string
  requires m >= 0
{
  if s == 0 then "-1"
  else if s > m * 9 then "-1"
  else
    var l := if 1 > s - 9 * (m - 1) then 1 else s - 9 * (m - 1);
    IntToString(l) + BuildMinDigitsSorted1118(BuildMinDigits1118(m - 1, s - l))
}

function BuildMinDigits1118(m: int, s: int): seq<int>
  decreases if m > 0 then m else 0
{
  if m <= 0 then []
  else if s > 9 then [9] + BuildMinDigits1118(m - 1, s - 9)
  else if 0 < s && s <= 9 then [s] + BuildMinDigits1118(m - 1, 0)
  else [0] + BuildMinDigits1118(m - 1, s)
}

function BuildMinDigitsSorted1118(lis: seq<int>): string
{
  JoinInts(SortInts(lis), "")
}
