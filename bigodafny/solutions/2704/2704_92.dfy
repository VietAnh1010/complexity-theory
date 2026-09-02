// 883_F. Lost in Transliteration  (problem 2704, solution 2704_92)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def replacement(str):
// 	str2 = str.replace("oo","u")
// 	str3 = str2.replace("kh","h")
// 	if str3 == str:
// 		return str3
// 	else :
// 		str3 = replacement(str3)
// 		return str3
// 	
// 	
// 
// 
// n = int(input())
// myList = []
// myList2 = []
// for i in range(n):
// 	myList.append(input())
// for x in myList:
// 	
// 	str4 = replacement(x)
// 	str4 = str4.replace("u","oo")
// 	str4 = str4.replace("h","kh")
// 	
// 	exist = False
// 	for str in myList2:
// 		if str4 == str:
// 			exist = True
// 	if exist == False:
// 		myList2.append(str4)
// 
// print(len(myList2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Reduce(s0: string) returns (result: string)
  decreases *
{
  var s := s0;
  var changed := true;
  while changed
    decreases *
  {
    var s2 := ReplaceAll(s, "oo", "u");
    var s3 := ReplaceAll(s2, "kh", "h");
    if s3 == s {
      changed := false;
    } else {
      s := s3;
    }
  }
  result := s;
}

method Solve(n: int, names: seq<string>) returns (output: string)
  requires n == |names|
  decreases *
{
  var result: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var str4 := Reduce(names[i]);
    str4 := ReplaceAll(str4, "u", "oo");
    str4 := ReplaceAll(str4, "h", "kh");
    var exists_ := false;
    var j := 0;
    while j < |result|
      invariant 0 <= j <= |result|
      decreases |result| - j
    {
      if result[j] == str4 { exists_ := true; }
      j := j + 1;
    }
    if !exists_ {
      result := result + [str4];
    }
    i := i + 1;
  }
  output := IntToString(|result|);
}
