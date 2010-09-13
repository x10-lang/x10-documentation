 package Statements.AreFor.Flatements;
 class Example {
 def example(var n:Int) {
  while (n > 1) {
     n = (n % 2 == 1) ? 3*n+1 : n/2;
  }
 } }