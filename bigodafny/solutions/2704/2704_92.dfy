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

method Solve(n: int, names: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
