 package statements.should.have.locals;
 class LocalExample {
 def example(a:Int) {
  if (a > 1) {
     val b = a/2;
     var c : Int = 0;
     // b and c are defined here
  }
  // b and c are not defined here.
} }