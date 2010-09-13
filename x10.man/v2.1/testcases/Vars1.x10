 package Vars.For.Squares;
class Counter {
  private var n : Int = 0;
  public def bump() : Int {
    val next = n+1;
    n = next;
    return next;
    }
}
