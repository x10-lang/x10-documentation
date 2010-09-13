package Vars.Local;
 class NotInitVal {
static def main(r: Rail[String]):Void {
  val a : Int;
  a = r.length;
  val b : String;
  if (a == 5) b = "five?"; else b = "" + a + " args";
  // ...
} }